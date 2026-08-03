/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.EvenSecretReduction
import FormalProof4FHE.TFHE.NativeTRGSWCVZRReduction

/-!
# Ordinary-RLWE Discharge of the Parity-Prefix CVZR Source

The generic native CVZR compiler reduces homogeneous zero-row security to RLWE whose secret is
supported on the public prefix coordinates.  A contiguous proper prefix is a genuine subspace
assumption.  This module records the technical way to avoid it when the target degree is doubled:
place the binary prefix in every even coefficient.

For a degree-`half` binary polynomial `p`, its target-ring embedding is `p(X²)`.  Splitting a
degree-`2 * half` sample into even and odd coefficients gives two ordinary degree-`half` binary
RLWE samples under the same `p`.  The source advantage is therefore exactly an ordinary RLWE
advantage with twice the row count.  Composing this equality with an exact CVZR compiler leaves
only ordinary binary-secret RLWE, with the pre-existing factor-two CVZR branch-selection loss.

This theorem concerns homogeneous zero rows.  It deliberately does not claim that the same
compiler constructs secret-message native TRGSW nonce rows.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.NativeTRGSWCVZRParityPrefix

noncomputable section

open Native.CoefficientStructuredLWE
open NativeTRGSWCVZRReduction
open DirectSubsetKeyBRK
open TGSW.RingSquare.TopWeightSampleExtraction

/-! ## Exact binary parity embedding -/

/-- Turn a binary coefficient vector into one degree-`half` ring element. -/
def binarySmallRq (q half : ℕ) (key : BinarySecret half) : RLWE.Rq q half :=
  (coefficientEquiv q half).symm (embedBinarySecret key)

/-- Rank-one small-ring binary secret. -/
def binarySmallSecret (q half : ℕ) (key : BinarySecret half) :
    RLWE.Secret q half :=
  fun _row ↦ binarySmallRq q half key

/-- Exact coefficientwise uniform-binary small-ring secret sampler. -/
def binarySmallSecretSampler (q half : ℕ) : ProbComp (RLWE.Secret q half) :=
  binarySmallSecret q half <$> ($ᵗ (BinarySecret half))

/-- The corresponding large-ring secret has the binary polynomial in its even coefficients. -/
def parityPrefixSecret (q half : ℕ) (key : BinarySecret half) :
    Fin 1 → RLWE.Rq q (2 * half) :=
  RLWE.EvenSecretReduction.evenSecretEmbed q half
    (binarySmallSecret q half key)

/-- Every even target coordinate is exactly the corresponding binary prefix digit. -/
theorem parityPrefixSecret_even (q half : ℕ) (key : BinarySecret half)
    (coordinate : Fin half) :
    coefficientEquiv q (2 * half) (parityPrefixSecret q half key 0)
        (RLWE.EvenOddDecomposition.parityIndexEquiv half (0, coordinate)) =
      embedBinarySecret key coordinate := by
  unfold parityPrefixSecret RLWE.EvenSecretReduction.evenSecretEmbed
    binarySmallSecret binarySmallRq
  rw [RLWE.EvenOddDecomposition.coefficientEquiv_joinRq_even]
  exact congrFun ((coefficientEquiv q half).apply_symm_apply
    (embedBinarySecret key)) coordinate

/-- Every odd target coordinate is zero. -/
theorem parityPrefixSecret_odd (q half : ℕ) (key : BinarySecret half)
    (coordinate : Fin half) :
    coefficientEquiv q (2 * half) (parityPrefixSecret q half key 0)
        (RLWE.EvenOddDecomposition.parityIndexEquiv half (1, coordinate)) = 0 := by
  unfold parityPrefixSecret RLWE.EvenSecretReduction.evenSecretEmbed
    binarySmallSecret
  simp

/-! ## Coefficient representation and KSK extraction -/

/-- Ordinary coefficient carrier of the doubled ring. -/
abbrev ParityCoefficients (q half : ℕ) := Coefficients q (2 * half)

/-- Put the binary prefix in the even coefficients of the doubled ring. -/
def parityPrefixCoefficients (q half : ℕ) (key : BinarySecret half) :
    ParityCoefficients q half :=
  (RLWE.EvenOddDecomposition.coefficientParityEquiv (ZMod q) half).symm
    (embedBinarySecret key, 0)

/-- Put an arbitrary known suffix in the odd coefficients of the doubled ring. -/
def paritySuffixCoefficients (q half : ℕ) (suffix : Fin half → ZMod q) :
    ParityCoefficients q half :=
  (RLWE.EvenOddDecomposition.coefficientParityEquiv (ZMod q) half).symm
    (0, suffix)

/-- Complete interleaved prefix/suffix coefficient vector. -/
def paritySplitCoefficients (q half : ℕ) (key : BinarySecret half)
    (suffix : Fin half → ZMod q) : ParityCoefficients q half :=
  (RLWE.EvenOddDecomposition.coefficientParityEquiv (ZMod q) half).symm
    (embedBinarySecret key, suffix)

/-- The two disjoint parity embeddings add to the complete split secret. -/
theorem parityPrefixCoefficients_add_suffixCoefficients
    (q half : ℕ) (key : BinarySecret half) (suffix : Fin half → ZMod q) :
    parityPrefixCoefficients q half key + paritySuffixCoefficients q half suffix =
      paritySplitCoefficients q half key suffix := by
  funext coordinate
  obtain ⟨⟨branch, index⟩, rfl⟩ :=
    (RLWE.EvenOddDecomposition.parityIndexEquiv half).surjective coordinate
  fin_cases branch <;>
    simp [parityPrefixCoefficients, paritySuffixCoefficients,
      paritySplitCoefficients]

/-- Publicly add the contribution of a known odd-coordinate suffix to one coefficient row. -/
def addParityKnownSuffixRow
    {q half : ℕ} (suffix : Fin half → ZMod q)
    (row : ParityCoefficients q half × ParityCoefficients q half) :
    ParityCoefficients q half × ParityCoefficients q half :=
  (row.1, row.2 +
    negacyclicProduct (paritySuffixCoefficients q half suffix) row.1)

/-- The public suffix translation changes an even-supported real row into a row under the full
interleaved secret, preserving the complete error. -/
theorem addParityKnownSuffixRow_real
    {q half : ℕ} (key : BinarySecret half) (suffix : Fin half → ZMod q)
    (challenge error : ParityCoefficients q half) :
    addParityKnownSuffixRow suffix
        (challenge,
          negacyclicProduct (parityPrefixCoefficients q half key) challenge + error) =
      (challenge,
        negacyclicProduct (paritySplitCoefficients q half key suffix) challenge + error) := by
  apply Prod.ext
  · rfl
  · simp only [addParityKnownSuffixRow]
    rw [← parityPrefixCoefficients_add_suffixCoefficients,
      NativeTRGSWCVZRReduction.negacyclicProduct_add_left]
    abel

/-- Remove the known odd-coordinate suffix contribution. -/
def removeParityKnownSuffixRow
    {q half : ℕ} (suffix : Fin half → ZMod q)
    (row : ParityCoefficients q half × ParityCoefficients q half) :
    ParityCoefficients q half × ParityCoefficients q half :=
  (row.1, row.2 -
    negacyclicProduct (paritySuffixCoefficients q half suffix) row.1)

@[simp]
theorem removeParityKnownSuffixRow_add
    {q half : ℕ} (suffix : Fin half → ZMod q)
    (row : ParityCoefficients q half × ParityCoefficients q half) :
    removeParityKnownSuffixRow suffix (addParityKnownSuffixRow suffix row) = row := by
  rcases row with ⟨challenge, body⟩
  simp [removeParityKnownSuffixRow, addParityKnownSuffixRow]

@[simp]
theorem addParityKnownSuffixRow_remove
    {q half : ℕ} (suffix : Fin half → ZMod q)
    (row : ParityCoefficients q half × ParityCoefficients q half) :
    addParityKnownSuffixRow suffix (removeParityKnownSuffixRow suffix row) = row := by
  rcases row with ⟨challenge, body⟩
  simp [removeParityKnownSuffixRow, addParityKnownSuffixRow]

/-- Known-suffix transport is a permutation of the complete mask/body carrier. -/
theorem addParityKnownSuffixRow_bijective
    {q half : ℕ} (suffix : Fin half → ZMod q) :
    Function.Bijective
      (addParityKnownSuffixRow suffix :
        (ParityCoefficients q half × ParityCoefficients q half) → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeParityKnownSuffixRow suffix,
      removeParityKnownSuffixRow_add suffix,
      addParityKnownSuffixRow_remove suffix⟩

/-- The same public translation preserves an exactly uniform complete row. -/
theorem addParityKnownSuffixRow_uniform_evalDist
    (q half : ℕ) [NeZero q] (suffix : Fin half → ZMod q) :
    evalDist (addParityKnownSuffixRow suffix <$>
        ($ᵗ (ParityCoefficients q half × ParityCoefficients q half))) =
      evalDist ($ᵗ (ParityCoefficients q half × ParityCoefficients q half)) :=
  evalDist_map_bijective_uniform_cross
    (α := ParityCoefficients q half × ParityCoefficients q half)
    (β := ParityCoefficients q half × ParityCoefficients q half)
    (addParityKnownSuffixRow suffix)
    (addParityKnownSuffixRow_bijective suffix)

/-- Coefficient presentation of the ring-valued even-secret embedding used by the source game. -/
theorem coefficientEquiv_evenSecretEmbed
    (q half : ℕ) (key : BinarySecret half) :
    coefficientEquiv q (2 * half)
        (RLWE.EvenSecretReduction.evenSecretEmbed q half
          (binarySmallSecret q half key) 0) =
      parityPrefixCoefficients q half key := by
  apply (RLWE.EvenOddDecomposition.coefficientParityEquiv
    (ZMod q) half).injective
  unfold RLWE.EvenSecretReduction.evenSecretEmbed
  rw [RLWE.EvenOddDecomposition.coefficientParityEquiv_joinRq]
  simp [binarySmallSecret,
    binarySmallRq, parityPrefixCoefficients]

/-- Parity splitting preserves coefficientwise addition. -/
theorem coefficientParityEquiv_add
    {R : Type} [Add R] (half : ℕ)
    (left right : Fin (2 * half) → R) :
    RLWE.EvenOddDecomposition.coefficientParityEquiv R half (left + right) =
      RLWE.EvenOddDecomposition.coefficientParityEquiv R half left +
        RLWE.EvenOddDecomposition.coefficientParityEquiv R half right := by
  apply Prod.ext
  · funext coordinate
    rfl
  · funext coordinate
    rfl

/-- Retain the mask of one even output coefficient.  Writing the half degree as
`smallDegree + 1` lets this reuse the checked nonempty negacyclic extraction equivalence without
introducing a cast-only theorem parameter. -/
def parityPrefixExtractedMask
    {q smallDegree : ℕ} (output : Fin (smallDegree + 1))
    (challenge : ParityCoefficients q (smallDegree + 1)) :
    Fin (smallDegree + 1) → ZMod q :=
  extractedMask output
    (RLWE.EvenOddDecomposition.coefficientParityEquiv
      (ZMod q) (smallDegree + 1) challenge).1

/-- Split a doubled-ring mask into parity halves and apply the signed extraction permutation to
the even half. -/
def paritySplitExtractedMaskEquiv
    (q smallDegree : ℕ) (output : Fin (smallDegree + 1)) :
    ParityCoefficients q (smallDegree + 1) ≃
      (Fin (smallDegree + 1) → ZMod q) ×
        (Fin (smallDegree + 1) → ZMod q) :=
  (RLWE.EvenOddDecomposition.coefficientParityEquiv
      (ZMod q) (smallDegree + 1)).trans
    ((extractedMaskEquiv output).prodCongr
      (Equiv.refl (Fin (smallDegree + 1) → ZMod q)))

@[simp]
theorem paritySplitExtractedMaskEquiv_fst
    {q smallDegree : ℕ} (output : Fin (smallDegree + 1))
    (challenge : ParityCoefficients q (smallDegree + 1)) :
    (paritySplitExtractedMaskEquiv q smallDegree output challenge).1 =
      parityPrefixExtractedMask output challenge := by
  rfl

/-- Selecting one even coefficient of a ring product by an even-supported binary secret gives
the exact scalar dot product under that binary key. -/
theorem evenSecretProduct_evenCoefficient_eq_dotProduct
    (q smallDegree : ℕ) [Nontrivial (ZMod q)]
    (key : BinarySecret (smallDegree + 1))
    (challenge : RLWE.Rq q (2 * (smallDegree + 1)))
    (output : Fin (smallDegree + 1)) :
    coefficientEquiv q (2 * (smallDegree + 1))
        (@Mul.mul (RLWE.Rq q (2 * (smallDegree + 1)))
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) (2 * (smallDegree + 1))).toMul
          (RLWE.EvenSecretReduction.evenSecretEmbed q (smallDegree + 1)
            (binarySmallSecret q (smallDegree + 1) key) 0)
          challenge)
        (RLWE.EvenOddDecomposition.parityIndexEquiv
          (smallDegree + 1) (0, output)) =
      dotProduct (embedBinarySecret key)
        (parityPrefixExtractedMask output
          (coefficientEquiv q (2 * (smallDegree + 1)) challenge)) := by
  let split := RLWE.EvenOddDecomposition.ringParityEquiv
    q (smallDegree + 1) challenge
  rw [show challenge = RLWE.EvenOddDecomposition.joinRq q (smallDegree + 1)
      split.1 split.2 by
    exact (RLWE.EvenOddDecomposition.joinRq_ringParityEquiv
      q (smallDegree + 1) challenge).symm]
  unfold RLWE.EvenSecretReduction.evenSecretEmbed binarySmallSecret
  rw [show
    @Mul.mul (RLWE.Rq q (2 * (smallDegree + 1)))
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) (2 * (smallDegree + 1))).toMul
        (RLWE.EvenOddDecomposition.joinRq q (smallDegree + 1)
          (binarySmallRq q (smallDegree + 1) key) 0)
        (RLWE.EvenOddDecomposition.joinRq q (smallDegree + 1) split.1 split.2) =
      @Mul.mul (RLWE.Rq q (2 * (smallDegree + 1)))
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) (2 * (smallDegree + 1))).toMul
        (RLWE.EvenOddDecomposition.joinRq q (smallDegree + 1) split.1 split.2)
        (RLWE.EvenOddDecomposition.joinRq q (smallDegree + 1)
          (binarySmallRq q (smallDegree + 1) key) 0) by
    exact mul_comm _ _]
  rw [RLWE.EvenOddDecomposition.joinRq_commRing_mul_even
    q (smallDegree + 1) (by omega)]
  rw [RLWE.EvenOddDecomposition.coefficientEquiv_joinRq_even]
  rw [show
    @Mul.mul (RLWE.Rq q (smallDegree + 1))
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) (smallDegree + 1)).toMul
        split.1 (binarySmallRq q (smallDegree + 1) key) =
      @Mul.mul (RLWE.Rq q (smallDegree + 1))
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) (smallDegree + 1)).toMul
        (binarySmallRq q (smallDegree + 1) key) split.1 by
    exact mul_comm _ _]
  rw [coefficientEquiv_semiring_mul]
  rw [negacyclicProduct_apply_eq_dotProduct]
  simp only [parityPrefixExtractedMask, binarySmallRq,
    Equiv.apply_symm_apply]
  rw [RLWE.EvenOddDecomposition.coefficientParityEquiv_joinRq]

/-- Coefficient-form version of the preceding ring identity. -/
theorem negacyclicProduct_parityPrefix_even_apply_eq_dotProduct
    {q smallDegree : ℕ} [Nontrivial (ZMod q)]
    (key : BinarySecret (smallDegree + 1))
    (challenge : ParityCoefficients q (smallDegree + 1))
    (output : Fin (smallDegree + 1)) :
    (RLWE.EvenOddDecomposition.coefficientParityEquiv
        (ZMod q) (smallDegree + 1)
        (negacyclicProduct
          (parityPrefixCoefficients q (smallDegree + 1) key) challenge)).1 output =
      dotProduct (embedBinarySecret key)
        (parityPrefixExtractedMask output challenge) := by
  let ringChallenge :=
    (coefficientEquiv q (2 * (smallDegree + 1))).symm challenge
  have h := evenSecretProduct_evenCoefficient_eq_dotProduct
    q smallDegree key ringChallenge output
  rw [coefficientEquiv_semiring_mul, coefficientEquiv_evenSecretEmbed] at h
  simpa [ringChallenge] using h

/-- For every fixed even output coefficient, the extracted prefix mask of a uniform doubled-ring
mask is exactly uniform on all half-degree vectors. -/
theorem parityPrefixExtractedMask_uniform_evalDist
    (q smallDegree : ℕ) [NeZero q] (output : Fin (smallDegree + 1)) :
    evalDist (parityPrefixExtractedMask output <$>
        ($ᵗ (ParityCoefficients q (smallDegree + 1)))) =
      evalDist ($ᵗ (Fin (smallDegree + 1) → ZMod q)) := by
  let split := paritySplitExtractedMaskEquiv q smallDegree output
  have hsplit :
      evalDist (split <$>
          ($ᵗ (ParityCoefficients q (smallDegree + 1)))) =
        evalDist ($ᵗ ((Fin (smallDegree + 1) → ZMod q) ×
          (Fin (smallDegree + 1) → ZMod q))) :=
    evalDist_map_bijective_uniform_cross
      (α := ParityCoefficients q (smallDegree + 1))
      (β := (Fin (smallDegree + 1) → ZMod q) ×
        (Fin (smallDegree + 1) → ZMod q))
      split split.bijective
  calc
    evalDist (parityPrefixExtractedMask output <$>
        ($ᵗ (ParityCoefficients q (smallDegree + 1)))) =
      evalDist (Prod.fst <$>
        (split <$> ($ᵗ (ParityCoefficients q (smallDegree + 1))))) := by
          congr 1
          rw [Functor.map_map]
          apply congrArg (fun transform ↦ transform <$>
            ($ᵗ (ParityCoefficients q (smallDegree + 1))))
          funext challenge
          exact (paritySplitExtractedMaskEquiv_fst output challenge).symm
    _ = evalDist (Prod.fst <$>
        ($ᵗ ((Fin (smallDegree + 1) → ZMod q) ×
          (Fin (smallDegree + 1) → ZMod q)))) :=
      evalDist_map_eq_of_evalDist_eq hsplit Prod.fst
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- Row-major collection of all parity-prefix masks. -/
def parityExtractedMaskRows
    {q smallDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (smallDegree + 1))
    (challenge : Fin rowCount → ParityCoefficients q (smallDegree + 1)) :
    Fin rowCount → (Fin (smallDegree + 1) → ZMod q) :=
  fun row ↦ parityPrefixExtractedMask (output row) (challenge row)

/-- Swapping the arguments of a finite function is a carrier equivalence. -/
def parityFunctionFlipEquiv (A B C : Type) :
    (A → B → C) ≃ (B → A → C) where
  toFun values b a := values a b
  invFun values a b := values b a
  left_inv _ := rfl
  right_inv _ := rfl

/-- All independently extracted row masks are jointly uniform. -/
theorem parityExtractedMaskRows_uniform_evalDist
    (q smallDegree rowCount : ℕ) [NeZero q]
    (output : Fin rowCount → Fin (smallDegree + 1)) :
    evalDist (parityExtractedMaskRows output <$>
        ($ᵗ (Fin rowCount → ParityCoefficients q (smallDegree + 1)))) =
      evalDist ($ᵗ (Fin rowCount →
        (Fin (smallDegree + 1) → ZMod q))) := by
  let RingMask := ParityCoefficients q (smallDegree + 1)
  let PrefixMask := Fin (smallDegree + 1) → ZMod q
  have hsource :=
    (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := RingMask) rowCount).symm
  have hmapped := evalDist_map_eq_of_evalDist_eq hsource
    (parityExtractedMaskRows output)
  have hcommute := FormalProof4FHE.FiniteProduct.map_fin_mOfFn rowCount
    (fun _ ↦ ($ᵗ RingMask : ProbComp RingMask))
    (fun row challenge ↦ parityPrefixExtractedMask (output row) challenge)
  have hrows :
      evalDist (Fin.mOfFn rowCount fun row ↦
          parityPrefixExtractedMask (output row) <$>
            ($ᵗ RingMask : ProbComp RingMask)) =
        evalDist (Fin.mOfFn rowCount fun _ ↦
          ($ᵗ PrefixMask : ProbComp PrefixMask)) := by
    apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    intro row
    exact parityPrefixExtractedMask_uniform_evalDist
      q smallDegree (output row)
  calc
    evalDist (parityExtractedMaskRows output <$>
        ($ᵗ (Fin rowCount → RingMask))) =
      evalDist (parityExtractedMaskRows output <$>
        ProbComp.sampleIID rowCount ($ᵗ RingMask)) := hmapped
    _ =
      evalDist (Fin.mOfFn rowCount fun row ↦
        parityPrefixExtractedMask (output row) <$>
          ($ᵗ RingMask : ProbComp RingMask)) := by
        change evalDist
            ((fun values row ↦
              parityPrefixExtractedMask (output row) (values row)) <$>
              Fin.mOfFn rowCount
                (fun _ ↦ ($ᵗ RingMask : ProbComp RingMask))) = _
        exact congrArg evalDist hcommute
    _ = evalDist (Fin.mOfFn rowCount fun _ ↦
          ($ᵗ PrefixMask : ProbComp PrefixMask)) := hrows
    _ = evalDist ($ᵗ (Fin rowCount → PrefixMask)) :=
      FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform rowCount

/-- Extract all prefix masks rowwise and transpose them into native batch-matrix order. -/
def parityExtractedMaskMatrix
    {q smallDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (smallDegree + 1))
    (challenge : Fin rowCount → ParityCoefficients q (smallDegree + 1)) :
    Matrix (Fin (smallDegree + 1)) (Fin rowCount) (ZMod q) :=
  fun coordinate row ↦
    parityPrefixExtractedMask (output row) (challenge row) coordinate

/-- Native matrix order of the complete extracted mask batch is jointly uniform. -/
theorem parityExtractedMaskMatrix_uniform_evalDist
    (q smallDegree rowCount : ℕ) [NeZero q]
    (output : Fin rowCount → Fin (smallDegree + 1)) :
    evalDist (parityExtractedMaskMatrix output <$>
        ($ᵗ (Fin rowCount → ParityCoefficients q (smallDegree + 1)))) =
      evalDist ($ᵗ (Matrix (Fin (smallDegree + 1))
        (Fin rowCount) (ZMod q))) := by
  have hrows := parityExtractedMaskRows_uniform_evalDist
    q smallDegree rowCount output
  let flip := parityFunctionFlipEquiv (Fin rowCount)
    (Fin (smallDegree + 1)) (ZMod q)
  have hflip :
      evalDist ((parityFunctionFlipEquiv (Fin rowCount)
          (Fin (smallDegree + 1)) (ZMod q) :
          (Fin rowCount → (Fin (smallDegree + 1) → ZMod q)) →
            Matrix (Fin (smallDegree + 1)) (Fin rowCount) (ZMod q)) <$>
          ($ᵗ (Fin rowCount → (Fin (smallDegree + 1) → ZMod q)))) =
        evalDist ($ᵗ (Matrix (Fin (smallDegree + 1))
          (Fin rowCount) (ZMod q))) :=
    evalDist_map_bijective_uniform_cross
      (α := Fin rowCount → (Fin (smallDegree + 1) → ZMod q))
      (β := Matrix (Fin (smallDegree + 1)) (Fin rowCount) (ZMod q))
      flip flip.bijective
  have hdefinition :
      evalDist (parityExtractedMaskMatrix output <$>
        ($ᵗ (Fin rowCount → ParityCoefficients q (smallDegree + 1)))) =
        evalDist ((parityFunctionFlipEquiv (Fin rowCount)
          (Fin (smallDegree + 1)) (ZMod q) :
          (Fin rowCount → (Fin (smallDegree + 1) → ZMod q)) →
            Matrix (Fin (smallDegree + 1)) (Fin rowCount) (ZMod q)) <$>
          (parityExtractedMaskRows output <$>
            ($ᵗ (Fin rowCount →
              ParityCoefficients q (smallDegree + 1))))) := by
    simp only [Functor.map_map]
    congr 1
  have hmapped :
      evalDist ((parityFunctionFlipEquiv (Fin rowCount)
          (Fin (smallDegree + 1)) (ZMod q) :
          (Fin rowCount → (Fin (smallDegree + 1) → ZMod q)) →
            Matrix (Fin (smallDegree + 1)) (Fin rowCount) (ZMod q)) <$>
        (parityExtractedMaskRows output <$>
          ($ᵗ (Fin rowCount → ParityCoefficients q (smallDegree + 1))))) =
        evalDist ((parityFunctionFlipEquiv (Fin rowCount)
          (Fin (smallDegree + 1)) (ZMod q) :
          (Fin rowCount → (Fin (smallDegree + 1) → ZMod q)) →
            Matrix (Fin (smallDegree + 1)) (Fin rowCount) (ZMod q)) <$>
          ($ᵗ (Fin rowCount →
            (Fin (smallDegree + 1) → ZMod q)))) :=
    evalDist_map_eq_of_evalDist_eq hrows flip
  exact hdefinition.trans (hmapped.trans hflip)

/-! ### Exact CBD coefficient law for the parity source -/

/-- One coefficient of the small-ring CBD sampler is exactly the scalar CBD law. -/
theorem smallCBDCoefficient_evalDist
    (q degree eta : ℕ) [NeZero q] (output : Fin degree) :
    evalDist ((fun error : RLWE.Rq q degree ↦
        coefficientEquiv q degree error output) <$>
      RLWE.CenteredBinomial.sampler q degree eta) =
      evalDist (CenteredBinomial.scalarSampler q eta) := by
  let select := fun coefficients : Fin degree → ZMod q ↦ coefficients output
  have hvectors :=
    RLWE.CenteredBinomial.coefficientVector_sampler_evalDist q degree eta
  have hselect := evalDist_map_eq_of_evalDist_eq hvectors select
  have hcoordinate :=
    FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply
      degree (fun _ ↦ RLWE.CenteredBinomial.coefficientSampler q eta)
      output id
  calc
    evalDist ((fun error : RLWE.Rq q degree ↦
        coefficientEquiv q degree error output) <$>
      RLWE.CenteredBinomial.sampler q degree eta) =
      evalDist (select <$> (RLWE.CenteredBinomial.coefficientVector <$>
        RLWE.CenteredBinomial.sampler q degree eta)) := by
          simp only [Functor.map_map]
          congr 1
    _ = evalDist (select <$> ProbComp.sampleIID degree
          (RLWE.CenteredBinomial.coefficientSampler q eta)) := hselect
    _ = evalDist (RLWE.CenteredBinomial.coefficientSampler q eta) := by
      simpa [ProbComp.sampleIID, select] using hcoordinate
    _ = evalDist (CenteredBinomial.scalarSampler q eta) := by
      congr 1
      simp [RLWE.CenteredBinomial.coefficientSampler,
        CenteredBinomial.scalarSampler, CenteredBinomial.scalarErrorFromCoins,
        map_eq_bind_pure_comp, monad_norm]

/-- Select one coefficient from the even half of a paired doubled-ring error. -/
def pairedEvenCoefficient
    {q half : ℕ} (output : Fin half) (error : RLWE.Rq q (2 * half)) : ZMod q :=
  coefficientEquiv q half
    (RLWE.EvenOddDecomposition.ringParityEquiv q half error).1 output

/-- A paired target-ring CBD error has exactly scalar CBD law at every selected even
coefficient. -/
theorem pairedEvenCoefficient_cbd_evalDist
    (q smallDegree eta : ℕ) [NeZero q]
    (output : Fin (smallDegree + 1)) :
    evalDist (pairedEvenCoefficient output <$>
        RLWE.EvenSecretReduction.pairedErrorSampler q (smallDegree + 1)
          (RLWE.CenteredBinomial.sampler q (smallDegree + 1) eta)) =
      evalDist (CenteredBinomial.scalarSampler q eta) := by
  let smallSampler :=
    RLWE.CenteredBinomial.sampler q (smallDegree + 1) eta
  have hnever : Pr[⊥ | smallSampler] = 0 := by
    simp [smallSampler,
      RLWE.CenteredBinomial.sampler_eq_map_uniformCoins]
  have hnormalize :
      evalDist (pairedEvenCoefficient output <$>
          RLWE.EvenSecretReduction.pairedErrorSampler q (smallDegree + 1)
            smallSampler) =
        evalDist (smallSampler >>= fun evenError ↦
          smallSampler >>= fun _oddError ↦
          pure (coefficientEquiv q (smallDegree + 1) evenError output)) := by
    simp [RLWE.EvenSecretReduction.pairedErrorSampler,
      RLWE.OddSecretReduction.pairedErrorSampler, pairedEvenCoefficient,
      map_eq_bind_pure_comp, bind_assoc, monad_norm]
  rw [hnormalize]
  calc
    evalDist (smallSampler >>= fun evenError ↦
        smallSampler >>= fun _oddError ↦
        pure (coefficientEquiv q (smallDegree + 1) evenError output)) =
      evalDist (smallSampler >>= fun evenError ↦
        pure (coefficientEquiv q (smallDegree + 1) evenError output)) := by
          refine evalDist_bind_congr' smallSampler fun evenError ↦ ?_
          exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
            smallSampler hnever
            (pure (coefficientEquiv q (smallDegree + 1) evenError output))
    _ = evalDist ((fun error : RLWE.Rq q (smallDegree + 1) ↦
        coefficientEquiv q (smallDegree + 1) error output) <$>
          smallSampler) := by
      simp [map_eq_bind_pure_comp]
    _ = _ := smallCBDCoefficient_evalDist q (smallDegree + 1) eta output

/-- Select an even-half coefficient from every row of a complete ring-error vector. -/
def pairedEvenErrorVector
    {q half rowCount : ℕ} (output : Fin rowCount → Fin half)
    (error : Fin rowCount → RLWE.Rq q (2 * half)) : Fin rowCount → ZMod q :=
  fun row ↦ pairedEvenCoefficient (output row) (error row)

/-- The entire selected KSK error vector from IID paired CBD rows is exactly IID scalar CBD. -/
theorem pairedEvenErrorVector_cbd_evalDist
    (q smallDegree rowCount eta : ℕ) [NeZero q]
    (output : Fin rowCount → Fin (smallDegree + 1)) :
    evalDist (pairedEvenErrorVector output <$>
        ProbComp.sampleIID rowCount
          (RLWE.EvenSecretReduction.pairedErrorSampler q (smallDegree + 1)
            (RLWE.CenteredBinomial.sampler q (smallDegree + 1) eta))) =
      evalDist (ProbComp.sampleIID rowCount
        (CenteredBinomial.scalarSampler q eta)) := by
  let pairedSampler :=
    RLWE.EvenSecretReduction.pairedErrorSampler q (smallDegree + 1)
      (RLWE.CenteredBinomial.sampler q (smallDegree + 1) eta)
  have hcommute := FormalProof4FHE.FiniteProduct.map_fin_mOfFn rowCount
    (fun _ ↦ pairedSampler)
    (fun row error ↦ pairedEvenCoefficient (output row) error)
  calc
    evalDist (pairedEvenErrorVector output <$>
        ProbComp.sampleIID rowCount pairedSampler) =
      evalDist (Fin.mOfFn rowCount fun row ↦
        pairedEvenCoefficient (output row) <$> pairedSampler) := by
          change evalDist
              ((fun values row ↦ pairedEvenCoefficient (output row) (values row)) <$>
                Fin.mOfFn rowCount (fun _ ↦ pairedSampler)) = _
          exact congrArg evalDist hcommute
    _ = evalDist (Fin.mOfFn rowCount fun _ ↦
        CenteredBinomial.scalarSampler q eta) := by
          apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
          intro row
          exact pairedEvenCoefficient_cbd_evalDist
            q smallDegree eta (output row)
    _ = _ := by rfl

/-- Select the corresponding even-half coefficient from every complete error row. -/
def paritySelectedErrorVector
    {q smallDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (smallDegree + 1))
    (error : Fin rowCount → ParityCoefficients q (smallDegree + 1)) :
    Fin rowCount → ZMod q :=
  fun row ↦
    (RLWE.EvenOddDecomposition.coefficientParityEquiv
      (ZMod q) (smallDegree + 1) (error row)).1 (output row)

/-- Public batched extraction of affine KSK rows from doubled-ring samples. -/
def extractParityKSKBatch
    {q smallDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (smallDegree + 1))
    (message : Fin rowCount → ZMod q)
    (samples : Fin rowCount →
      ParityCoefficients q (smallDegree + 1) ×
        ParityCoefficients q (smallDegree + 1)) :
    TLWE.BatchCiphertext (ZMod q) (smallDegree + 1) rowCount :=
  (fun coordinate row ↦
      parityPrefixExtractedMask (output row) (samples row).1 coordinate,
    fun row ↦
      (RLWE.EvenOddDecomposition.coefficientParityEquiv
        (ZMod q) (smallDegree + 1) (samples row).2).1 (output row) + message row)

/-- Complete real-source extraction identity.  In particular, the joint error is the displayed
selected coefficient vector; it is not replaced by a collection of marginal claims. -/
theorem extractParityKSKBatch_real
    {q smallDegree rowCount : ℕ} [Nontrivial (ZMod q)]
    (key : BinarySecret (smallDegree + 1))
    (challenge error : Fin rowCount →
      ParityCoefficients q (smallDegree + 1))
    (output : Fin rowCount → Fin (smallDegree + 1))
    (message : Fin rowCount → ZMod q) :
    extractParityKSKBatch output message
        (fun row ↦
          (challenge row,
            negacyclicProduct
                (parityPrefixCoefficients q (smallDegree + 1) key)
                (challenge row) + error row)) =
      TLWE.batchAssemble (embedBinarySecret key)
        (parityExtractedMaskMatrix output challenge)
        message (paritySelectedErrorVector output error) := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [extractParityKSKBatch, TLWE.batchAssemble, Pi.add_apply,
      Matrix.vecMul]
    rw [coefficientParityEquiv_add]
    change
      (RLWE.EvenOddDecomposition.coefficientParityEquiv
          (ZMod q) (smallDegree + 1)
          (negacyclicProduct
            (parityPrefixCoefficients q (smallDegree + 1) key)
            (challenge row))).1 (output row) +
          (RLWE.EvenOddDecomposition.coefficientParityEquiv
            (ZMod q) (smallDegree + 1) (error row)).1 (output row) +
        message row = _
    rw [negacyclicProduct_parityPrefix_even_apply_eq_dotProduct]
    change
      dotProduct (embedBinarySecret key)
          (parityPrefixExtractedMask (output row) (challenge row)) +
            paritySelectedErrorVector output error row + message row =
        dotProduct (embedBinarySecret key)
            (parityPrefixExtractedMask (output row) (challenge row)) + message row +
          paritySelectedErrorVector output error row
    abel

/-! ## Parity-prefix source and ordinary RLWE -/

/-- The parity-prefix CVZR source.  Each target-ring error is explicitly the interleaving of two
independent samples from the small-ring error law. -/
noncomputable def parityPrefixProblem
    (q half samples : ℕ) [NeZero q]
    (smallErrorSampler : ProbComp (RLWE.Rq q half)) :=
  RLWE.EvenSecretReduction.evenProblem q half samples
    (binarySmallSecretSampler q half) smallErrorSampler

/-- Conventional degree-`half` binary-secret RLWE with twice the source row count. -/
noncomputable def smallBinaryRLWEProblem
    (q half samples : ℕ) [NeZero q]
    (smallErrorSampler : ProbComp (RLWE.Rq q half)) :=
  RLWE.problem q half (2 * samples)
    (binarySmallSecretSampler q half) smallErrorSampler

/-- Exact public preprocessing from a parity-prefix source adversary to ordinary binary RLWE. -/
def ordinaryRLWEReduction
    {q half samples : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    {smallErrorSampler : ProbComp (RLWE.Rq q half)}
    (adversary : LearningWithErrors.Adversary
      (parityPrefixProblem q half samples smallErrorSampler)) :
    LearningWithErrors.Adversary
      (smallBinaryRLWEProblem q half samples smallErrorSampler) :=
  RLWE.EvenSecretReduction.reduction adversary

/-- The parity-prefix source advantage is exactly ordinary half-degree binary RLWE advantage. -/
theorem parityPrefixAdvantage_eq_smallBinaryRLWE
    (q half samples : ℕ) [NeZero q] [Nontrivial (ZMod q)]
    (hhalf : 0 < half)
    (smallErrorSampler : ProbComp (RLWE.Rq q half))
    (adversary : LearningWithErrors.Adversary
      (parityPrefixProblem q half samples smallErrorSampler)) :
    LearningWithErrors.advantage
        (parityPrefixProblem q half samples smallErrorSampler) adversary =
      LearningWithErrors.advantage
        (smallBinaryRLWEProblem q half samples smallErrorSampler)
        (ordinaryRLWEReduction adversary) := by
  exact RLWE.EvenSecretReduction.advantage_eq_smallRLWE
    q half samples hhalf (binarySmallSecretSampler q half) smallErrorSampler adversary

/-! ## Composition with the exact CVZR compiler -/

/-- The ordinary-RLWE adversary obtained by composing CVZR branch selection with exact parity
splitting. -/
noncomputable def cvzrOrdinaryRLWEReduction
    {q half samples : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    {smallErrorSampler : ProbComp (RLWE.Rq q half)}
    {Known View : Type}
    {knownSampler : ProbComp Known} {targetView : Bool → ProbComp View}
    (compiler : ExactCVZRCompiler
      (parityPrefixProblem q half samples smallErrorSampler)
      knownSampler targetView)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.Adversary
      (smallBinaryRLWEProblem q half samples smallErrorSampler) :=
  ordinaryRLWEReduction (compiler.reduction distinguisher)

/-- Technical CVZR endpoint theorem: an exact compiler from the parity-prefix source leaves only
ordinary binary-secret RLWE.  The factor two is exactly the CVZR branch-selection loss and is not
multiplied by the number of rows. -/
theorem targetAdvantage_le_two_smallBinaryRLWE
    {q half samples : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    (hhalf : 0 < half)
    {smallErrorSampler : ProbComp (RLWE.Rq q half)}
    {Known View : Type}
    {knownSampler : ProbComp Known} {targetView : Bool → ProbComp View}
    (compiler : ExactCVZRCompiler
      (parityPrefixProblem q half samples smallErrorSampler)
      knownSampler targetView)
    (distinguisher : Distinguisher View) :
    DirectSubsetKeyBRK.targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage
        (smallBinaryRLWEProblem q half samples smallErrorSampler)
        (cvzrOrdinaryRLWEReduction compiler distinguisher) := by
  have hsource := compiler.targetAdvantage_le_two_source distinguisher
  rw [parityPrefixAdvantage_eq_smallBinaryRLWE
    q half samples hhalf smallErrorSampler] at hsource
  exact hsource

/-- The selected ordinary-RLWE adversary has exactly half of the target CVZR advantage. -/
theorem cvzrOrdinaryRLWEReduction_advantage_eq_half
    {q half samples : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    (hhalf : 0 < half)
    {smallErrorSampler : ProbComp (RLWE.Rq q half)}
    {Known View : Type}
    {knownSampler : ProbComp Known} {targetView : Bool → ProbComp View}
    (compiler : ExactCVZRCompiler
      (parityPrefixProblem q half samples smallErrorSampler)
      knownSampler targetView)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.advantage
        (smallBinaryRLWEProblem q half samples smallErrorSampler)
        (cvzrOrdinaryRLWEReduction compiler distinguisher) =
      DirectSubsetKeyBRK.targetAdvantage targetView distinguisher / 2 := by
  change LearningWithErrors.advantage
      (smallBinaryRLWEProblem q half samples smallErrorSampler)
      (ordinaryRLWEReduction (compiler.reduction distinguisher)) = _
  rw [← parityPrefixAdvantage_eq_smallBinaryRLWE
    q half samples hhalf smallErrorSampler]
  exact compiler.reduction_advantage_eq_half_targetAdvantage distinguisher

/-- A conventional binary-RLWE bound discharges the complete technical parity-prefix CVZR
source. -/
theorem targetAdvantage_le_of_smallBinaryRLWE
    {q half samples : ℕ} [NeZero q] [Nontrivial (ZMod q)]
    (hhalf : 0 < half)
    {smallErrorSampler : ProbComp (RLWE.Rq q half)}
    {Known View : Type}
    {knownSampler : ProbComp Known} {targetView : Bool → ProbComp View}
    (compiler : ExactCVZRCompiler
      (parityPrefixProblem q half samples smallErrorSampler)
      knownSampler targetView)
    (distinguisher : Distinguisher View)
    (epsilon : ℝ)
    (hRLWE : ∀ adversary : LearningWithErrors.Adversary
        (smallBinaryRLWEProblem q half samples smallErrorSampler),
      LearningWithErrors.advantage
        (smallBinaryRLWEProblem q half samples smallErrorSampler) adversary ≤ epsilon) :
    DirectSubsetKeyBRK.targetAdvantage targetView distinguisher ≤ 2 * epsilon := by
  calc
    DirectSubsetKeyBRK.targetAdvantage targetView distinguisher ≤
        2 * LearningWithErrors.advantage
          (smallBinaryRLWEProblem q half samples smallErrorSampler)
          (cvzrOrdinaryRLWEReduction compiler distinguisher) :=
      targetAdvantage_le_two_smallBinaryRLWE hhalf compiler distinguisher
    _ ≤ 2 * epsilon := by gcongr; exact hRLWE _

end

end FormalProof4FHE.TFHE.NativeTRGSWCVZRParityPrefix
