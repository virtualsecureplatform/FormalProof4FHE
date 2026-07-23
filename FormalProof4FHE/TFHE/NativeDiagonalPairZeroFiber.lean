/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalPairBinaryRank
import Mathlib.FieldTheory.Finiteness

/-!
# Rank-Sensitive Zero-Fiber Bounds for the Native TFHE Diagonal

The full-rank theorem for the native paired diagonal makes the challenge collision excess vanish,
but treating every deficient binary rectangle by the square of the whole challenge cardinality is
far too coarse.  This file records the exact finite-group identity

`zeroFiberCard * imageCard = domainCard`

and relates the native image to the image after coefficient parity reduction.  A surjective ring
map sends the native matrix image onto the reduced matrix image.  Consequently a reduced matrix of
rank `r` first forces at least `|F|^r` native image points.  When the reduction is also local, a
basis of the reduced image lifts to a free native image with at least `|R|^r` points.  Specializing
to native parity gives a sound rank-sensitive upper bound for every deficient pair.

This free-image estimate deliberately does not claim to be negligible for production parameters:
residue corank `t` can still leave a factor `|R|^t`, and parity rank forgets the higher `2`-adic and
`(X - 1)`-adic image distribution.  The result makes the additional quantitative input needed by
a production proof explicit.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-! ## Images under coefficient reduction -/

/-- Coefficient reduction sends the image of a native matrix-vector map into the image of the
reduced matrix-vector map. -/
def matrixRangeReductionMap
    {R S rowIndex columnIndex : Type}
    [CommRing R] [Field S]
    [Fintype rowIndex] [Fintype columnIndex]
    (hom : R →+* S) (matrix : Matrix rowIndex columnIndex R) :
    (matrix.mulVecLin.toAddMonoidHom).range →
      LinearMap.range (matrix.map hom).mulVecLin := fun value => by
  refine ⟨fun row => hom (value.1 row), ?_⟩
  obtain ⟨input, hinput⟩ := value.2
  refine ⟨hom ∘ input, ?_⟩
  funext row
  calc
    ((matrix.map hom) *ᵥ (hom ∘ input)) row =
        hom ((matrix *ᵥ input) row) :=
      (RingHom.map_mulVec hom matrix input row).symm
    _ = hom (value.1 row) := congrArg hom (congrFun hinput row)

@[simp]
theorem matrixRangeReductionMap_apply
    {R S rowIndex columnIndex : Type}
    [CommRing R] [Field S]
    [Fintype rowIndex] [Fintype columnIndex]
    (hom : R →+* S) (matrix : Matrix rowIndex columnIndex R)
    (value : (matrix.mulVecLin.toAddMonoidHom).range) :
    (matrixRangeReductionMap hom matrix value).1 =
      fun row => hom (value.1 row) := by
  rfl

/-- If coefficient reduction is surjective, the induced map between matrix images is
surjective as well. -/
theorem matrixRangeReductionMap_surjective
    {R S rowIndex columnIndex : Type}
    [CommRing R] [Field S]
    [Fintype rowIndex] [Fintype columnIndex]
    (hom : R →+* S) (hom_surjective : Function.Surjective hom)
    (matrix : Matrix rowIndex columnIndex R) :
    Function.Surjective (matrixRangeReductionMap hom matrix) := by
  classical
  intro value
  obtain ⟨input, hinput⟩ := value.2
  choose liftedInput hliftedInput using
    fun column : columnIndex => hom_surjective (input column)
  refine ⟨⟨matrix *ᵥ liftedInput, ⟨liftedInput, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  funext row
  rw [matrixRangeReductionMap_apply]
  calc
    hom ((matrix *ᵥ liftedInput) row) =
        ((matrix.map hom) *ᵥ (hom ∘ liftedInput)) row :=
      RingHom.map_mulVec hom matrix liftedInput row
    _ = ((matrix.map hom) *ᵥ input) row := by
      rw [show hom ∘ liftedInput = input by
        funext column
        exact hliftedInput column]
    _ = value.1 row := congrFun hinput row

/-- Rectangular injectivity lifts through a surjective local homomorphism.  The proof applies the
existing rectangular surjectivity lift to the transpose, obtains a right inverse there, and
transposes it into a left inverse of the original matrix. -/
theorem mulVec_injective_of_map_mulVec_injective
    {R S rowIndex columnIndex : Type}
    [CommRing R] [Field S]
    [Fintype rowIndex] [DecidableEq rowIndex]
    [Fintype columnIndex] [DecidableEq columnIndex]
    (hom : R →+* S) [IsLocalHom hom]
    (hom_surjective : Function.Surjective hom)
    (matrix : Matrix rowIndex columnIndex R)
    (mapped_injective : Function.Injective (matrix.map hom).mulVec) :
    Function.Injective matrix.mulVec := by
  have transpose_surjective : Function.Surjective matrix.transpose.mulVec := by
    apply mulVec_surjective_of_map_transpose_mulVec_injective
      hom hom_surjective matrix.transpose
    simpa only [Matrix.transpose_map, Matrix.transpose_transpose] using mapped_injective
  obtain ⟨rightInverse, transpose_mul_rightInverse⟩ :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mp transpose_surjective
  have leftInverse_mul : rightInverse.transpose * matrix = 1 := by
    calc
      rightInverse.transpose * matrix =
          (matrix.transpose * rightInverse).transpose := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = 1 := by rw [transpose_mul_rightInverse, Matrix.transpose_one]
  intro left right heq
  have hleft := congrArg rightInverse.transpose.mulVec heq
  simpa only [Matrix.mulVec_mulVec, leftInverse_mul, Matrix.one_mulVec] using hleft

/-- If a factored family of native columns remains independent after local coefficient
reduction, then the original native matrix image contains a free copy of the factor's complete
coefficient space. -/
theorem card_pow_width_le_card_matrixRange_of_mappedFactor_injective
    {R S rowIndex columnIndex basisIndex : Type}
    [CommRing R] [Field S]
    [Fintype rowIndex] [DecidableEq rowIndex]
    [Fintype columnIndex] [DecidableEq columnIndex]
    [Fintype basisIndex] [DecidableEq basisIndex]
    [Fintype R] [DecidableEq R]
    (hom : R →+* S) [IsLocalHom hom]
    (hom_surjective : Function.Surjective hom)
    (matrix : Matrix rowIndex columnIndex R)
    (factor : Matrix columnIndex basisIndex R)
    (mappedFactor_injective : Function.Injective
      ((matrix * factor).map hom).mulVec) :
    Fintype.card R ^ Fintype.card basisIndex ≤
      Fintype.card matrix.mulVecLin.toAddMonoidHom.range := by
  classical
  have factor_injective : Function.Injective (matrix * factor).mulVec :=
    mulVec_injective_of_map_mulVec_injective
      hom hom_surjective (matrix * factor) mappedFactor_injective
  let imageEmbedding : (basisIndex → R) →
      matrix.mulVecLin.toAddMonoidHom.range := fun values =>
    ⟨(matrix * factor) *ᵥ values, ⟨factor *ᵥ values, by
      exact Matrix.mulVec_mulVec values matrix factor⟩⟩
  have imageEmbedding_injective : Function.Injective imageEmbedding := by
    intro left right heq
    apply factor_injective
    exact congrArg Subtype.val heq
  simpa only [Fintype.card_fun] using
    Fintype.card_le_of_injective imageEmbedding imageEmbedding_injective

/-- A residue-field matrix of rank `r` forces the native image to contain a free `R^r`
submodule.  A basis of the reduced image is lifted to native input columns; its reduced column
matrix is injective, and the local-homomorphism lift supplies native injectivity. -/
theorem card_pow_mappedRank_le_card_matrixRange_of_local
    {R S rowIndex columnIndex : Type}
    [CommRing R] [Field S]
    [Fintype rowIndex] [DecidableEq rowIndex]
    [Fintype columnIndex] [DecidableEq columnIndex]
    [Fintype R] [DecidableEq R]
    (hom : R →+* S) [IsLocalHom hom]
    (hom_surjective : Function.Surjective hom)
    (matrix : Matrix rowIndex columnIndex R) :
    Fintype.card R ^ (matrix.map hom).rank ≤
      Fintype.card matrix.mulVecLin.toAddMonoidHom.range := by
  classical
  let mappedMatrix := matrix.map hom
  let Range := LinearMap.range mappedMatrix.mulVecLin
  let rangeBasis : Module.Basis (Fin mappedMatrix.rank) S Range :=
    Module.finBasisOfFinrankEq S Range (by rfl)
  let reducedPreimage : Fin mappedMatrix.rank → (columnIndex → S) :=
    fun index => Classical.choose (rangeBasis index).2
  have reducedPreimage_spec (index : Fin mappedMatrix.rank) :
      mappedMatrix *ᵥ reducedPreimage index = (rangeBasis index).1 :=
    Classical.choose_spec (rangeBasis index).2
  let reducedFactor : Matrix columnIndex (Fin mappedMatrix.rank) S :=
    fun column index => reducedPreimage index column
  have product_col (index : Fin mappedMatrix.rank) :
      (mappedMatrix * reducedFactor).col index =
        ((LinearMap.range mappedMatrix.mulVecLin).subtype ∘ rangeBasis) index := by
    funext row
    change (mappedMatrix *ᵥ reducedPreimage index) row =
      (rangeBasis index).1 row
    exact congrFun (reducedPreimage_spec index) row
  have rangeBasis_ambient : LinearIndependent S
      ((LinearMap.range mappedMatrix.mulVecLin).subtype ∘ rangeBasis) := by
    exact rangeBasis.linearIndependent.map
      (f := (LinearMap.range mappedMatrix.mulVecLin).subtype) (by simp)
  have reducedProduct_injective : Function.Injective
      (mappedMatrix * reducedFactor).mulVec := by
    rw [Matrix.mulVec_injective_iff]
    rw [show (mappedMatrix * reducedFactor).col =
        ((LinearMap.range mappedMatrix.mulVecLin).subtype ∘ rangeBasis) by
      funext index
      exact product_col index]
    exact rangeBasis_ambient
  let liftedFactor : Matrix columnIndex (Fin mappedMatrix.rank) R :=
    fun column index => Function.surjInv hom_surjective (reducedFactor column index)
  have liftedFactor_map : liftedFactor.map hom = reducedFactor := by
    ext column index
    exact Function.surjInv_eq hom_surjective _
  have hfree := card_pow_width_le_card_matrixRange_of_mappedFactor_injective
    hom hom_surjective matrix liftedFactor (by
      rw [Matrix.map_mul, liftedFactor_map]
      exact reducedProduct_injective)
  simpa only [Fintype.card_fin, mappedMatrix] using hfree

/-- The residue-field rank lower-bounds the cardinality of the native matrix image. -/
theorem card_pow_rank_le_card_matrixRange_of_surjective
    {R S rowIndex columnIndex : Type}
    [CommRing R] [Field S] [Finite S]
    [Fintype rowIndex] [Fintype columnIndex]
    [Fintype R] [DecidableEq R]
    (hom : R →+* S) (hom_surjective : Function.Surjective hom)
    (matrix : Matrix rowIndex columnIndex R) :
    Nat.card S ^ (matrix.map hom).rank ≤
      Nat.card (matrix.mulVecLin.toAddMonoidHom).range := by
  classical
  have hcard := Nat.card_le_card_of_surjective
    (matrixRangeReductionMap hom matrix)
    (matrixRangeReductionMap_surjective hom hom_surjective matrix)
  rw [Module.natCard_eq_pow_finrank
    (K := S) (V := LinearMap.range (matrix.map hom).mulVecLin)] at hcard
  change Nat.card S ^ (matrix.map hom).rank ≤
    Nat.card (matrix.mulVecLin.toAddMonoidHom).range at hcard
  exact hcard

/-! ## Exact paired image/zero-fiber accounting -/

/-- The matrix presentation and product-vector presentation of the paired row operator have the
same additive range. -/
theorem pairedRowDifferenceAddHom_range_eq_pairedRowMatrix_range
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    (pairedRowDifferenceAddHom candidate leftDigits rightDigits).range =
      (pairedRowMatrix candidate leftDigits rightDigits).mulVecLin.toAddMonoidHom.range := by
  ext output
  constructor
  · rintro ⟨values, rfl⟩
    refine ⟨pairedRowInputEquiv R (TGSW.rowCount dimension levels) values, ?_⟩
    change pairedRowMatrix candidate leftDigits rightDigits *ᵥ
        pairedRowInputEquiv R (TGSW.rowCount dimension levels) values =
      pairedRowDifferenceOperator candidate leftDigits rightDigits values
    exact pairedRowMatrix_mulVec_pairedRowInput
      candidate leftDigits rightDigits values
  · rintro ⟨combinedInput, rfl⟩
    let values :=
      (pairedRowInputEquiv R (TGSW.rowCount dimension levels)).symm combinedInput
    refine ⟨values, ?_⟩
    change pairedRowDifferenceOperator candidate leftDigits rightDigits values =
      pairedRowMatrix candidate leftDigits rightDigits *ᵥ combinedInput
    calc
      pairedRowDifferenceOperator candidate leftDigits rightDigits values =
          pairedRowMatrix candidate leftDigits rightDigits *ᵥ
            pairedRowInputEquiv R (TGSW.rowCount dimension levels) values :=
        (pairedRowMatrix_mulVec_pairedRowInput
          candidate leftDigits rightDigits values).symm
      _ = pairedRowMatrix candidate leftDigits rightDigits *ᵥ combinedInput := by
        congr 1
        exact (pairedRowInputEquiv R
          (TGSW.rowCount dimension levels)).apply_symm_apply combinedInput

/-- Cardinality form of the equality between the two presentations of the paired row image. -/
theorem pairedRowDifferenceAddHom_range_card_eq_pairedRowMatrix_range_card
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    Fintype.card
        (pairedRowDifferenceAddHom candidate leftDigits rightDigits).range =
      Fintype.card
        (pairedRowMatrix candidate leftDigits rightDigits).mulVecLin.toAddMonoidHom.range := by
  classical
  let rangeEquality := pairedRowDifferenceAddHom_range_eq_pairedRowMatrix_range
    candidate leftDigits rightDigits
  let typeEquality :
      (pairedRowDifferenceAddHom candidate leftDigits rightDigits).range =
        (pairedRowMatrix candidate leftDigits
          rightDigits).mulVecLin.toAddMonoidHom.range := rangeEquality
  exact Fintype.card_congr (Equiv.cast (congrArg
    (fun range : AddSubgroup
      (Fin (TGSW.rowCount dimension levels) → R) => (↑range : Type)) typeEquality))

/-- Exact finite-group identity for the paired row operator: its zero fiber times its image is
the complete paired row-input space. -/
theorem pairedRowZeroFiberCard_mul_imageCard_eq_domainCard
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    pairedRowZeroFiberCard candidate leftDigits rightDigits *
        Fintype.card
          (pairedRowDifferenceAddHom candidate leftDigits rightDigits).range =
      Fintype.card
        ((Fin (TGSW.rowCount dimension levels) → R) ×
          (Fin (TGSW.rowCount dimension levels) → R)) := by
  unfold pairedRowZeroFiberCard
  change
    (Finset.univ.filter fun values =>
        pairedRowDifferenceAddHom candidate leftDigits rightDigits values = 0).card *
          Fintype.card
            (pairedRowDifferenceAddHom candidate leftDigits rightDigits).range = _
  exact
    FormalProof4FHE.ConditionalCollision.zeroFiberCard_mul_card_range_addHom_eq_card
      (pairedRowDifferenceAddHom candidate leftDigits rightDigits)

/-! ## Native binary-rank specialization -/

/-- Cardinality of the native paired row image for two fixed difference ciphertexts. -/
def differencePairRowImageCard [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℕ :=
  Fintype.card
    (pairedRowDifferenceAddHom candidate
      (differenceEntryDigits params leftDifference)
      (differenceEntryDigits params rightDifference)).range

/-- Binary rank supplies a lower bound on the native paired-row image cardinality for every
difference pair, not just for full-rank pairs. -/
theorem two_pow_differencePairBinaryRank_le_rowImageCard [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    2 ^ (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank ≤
      differencePairRowImageCard params candidate
        leftDifference rightDifference := by
  let nativeMatrix := pairedRowMatrix candidate
    (differenceEntryDigits params leftDifference)
    (differenceEntryDigits params rightDifference)
  have hcard := card_pow_rank_le_card_matrixRange_of_surjective
    (rqParityEval heven (Nat.succ_pos degree))
    (ZMod.ringHom_surjective (rqParityEval heven (Nat.succ_pos degree)))
    nativeMatrix
  have hrank :
      (nativeMatrix.map (rqParityEval heven (Nat.succ_pos degree))).rank =
        (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank := by
    dsimp only [nativeMatrix]
    rw [rqParityEval_mapMatrix_pairedRowMatrix_difference]
    exact Matrix.rank_transpose _
  rw [hrank, Nat.card_eq_fintype_card, ZMod.card] at hcard
  calc
    2 ^ (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank ≤
      Fintype.card
        nativeMatrix.mulVecLin.toAddMonoidHom.range := by
          simpa only [Nat.card_eq_fintype_card] using hcard
    _ = differencePairRowImageCard params candidate
        leftDifference rightDifference := by
      unfold differencePairRowImageCard
      exact (pairedRowDifferenceAddHom_range_card_eq_pairedRowMatrix_range_card
        candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference)).symm

/-- Residue-field rank gives a product-form upper bound on the native paired zero fiber.  This
form avoids division and remains meaningful over natural cardinalities. -/
theorem pairedRowZeroFiberCard_mul_two_pow_binaryRank_le_domainCard [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) *
        2 ^ (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank ≤
      Fintype.card
        ((Fin (TGSW.rowCount ringRank params.levels) →
            RLWE.Rq q (degree + 1)) ×
          (Fin (TGSW.rowCount ringRank params.levels) →
            RLWE.Rq q (degree + 1))) := by
  calc
    pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) *
        2 ^ (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank ≤
      pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) *
        differencePairRowImageCard params candidate
          leftDifference rightDifference :=
        Nat.mul_le_mul_left _
          (two_pow_differencePairBinaryRank_le_rowImageCard
            params heven candidate leftDifference rightDifference)
    _ = _ := by
      exact pairedRowZeroFiberCard_mul_imageCard_eq_domainCard
        candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference)

/-- Division form of the rank-sensitive row zero-fiber estimate. -/
theorem pairedRowZeroFiberCard_le_domainCard_div_two_pow_binaryRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    (pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) : ℝ) ≤
      (Fintype.card
          ((Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1)) ×
            (Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1))) : ℝ) /
        (2 : ℝ) ^ (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank := by
  apply (le_div_iff₀ (by positivity :
    (0 : ℝ) < (2 : ℝ) ^ (differencePairBinaryTransposeMatrix params
      (leftDifference, rightDifference)).rank)).2
  exact_mod_cast pairedRowZeroFiberCard_mul_two_pow_binaryRank_le_domainCard
    params heven candidate leftDifference rightDifference

/-- Complete fixed-pair challenge collisions inherit the row-level residue-rank estimate. -/
theorem differencePairChallengeCollisionCount_le_of_binaryRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionCount params candidate
        leftDifference rightDifference ≤
      ((Fintype.card
          ((Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1)) ×
            (Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1))) : ℝ) /
        (2 : ℝ) ^ (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank) ^ ringRank := by
  unfold differencePairChallengeCollisionCount
  rw [pairedChallengeCollisionCount_eq_rowZeroFiberCard_pow]
  exact pow_le_pow_left₀ (by positivity)
    (pairedRowZeroFiberCard_le_domainCard_div_two_pow_binaryRank
      params heven candidate leftDifference rightDifference) ringRank

/-- The corresponding explicit upper bound on one pair's excess above the uniform challenge
baseline. -/
theorem differencePairChallengeCollisionExcess_le_of_binaryRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionExcess params candidate
        leftDifference rightDifference ≤
      ((Fintype.card
          ((Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1)) ×
            (Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1))) : ℝ) /
        (2 : ℝ) ^ (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank) ^ ringRank -
      Fintype.card (DiagonalChallenge q degree ringRank params.levels) := by
  unfold differencePairChallengeCollisionExcess
  linarith [differencePairChallengeCollisionCount_le_of_binaryRank
    params heven candidate leftDifference rightDifference]

/-- With the local-ring premise, binary rank `r` forces a free native image of cardinality
`|Rq|^r`, rather than merely the `2^r` points visible after parity reduction. -/
theorem rq_card_pow_differencePairBinaryRank_le_rowImageCard [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    Fintype.card (RLWE.Rq q (degree + 1)) ^
        (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank ≤
      differencePairRowImageCard params candidate
        leftDifference rightDifference := by
  letI : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)) := localParity
  let nativeMatrix := pairedRowMatrix candidate
    (differenceEntryDigits params leftDifference)
    (differenceEntryDigits params rightDifference)
  have hcard := card_pow_mappedRank_le_card_matrixRange_of_local
    (rqParityEval heven (Nat.succ_pos degree))
    (ZMod.ringHom_surjective (rqParityEval heven (Nat.succ_pos degree)))
    nativeMatrix
  have hrank :
      (nativeMatrix.map (rqParityEval heven (Nat.succ_pos degree))).rank =
        (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank := by
    dsimp only [nativeMatrix]
    rw [rqParityEval_mapMatrix_pairedRowMatrix_difference]
    exact Matrix.rank_transpose _
  rw [hrank] at hcard
  calc
    Fintype.card (RLWE.Rq q (degree + 1)) ^
        (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank ≤
      Fintype.card nativeMatrix.mulVecLin.toAddMonoidHom.range := hcard
    _ = differencePairRowImageCard params candidate
        leftDifference rightDifference := by
      unfold differencePairRowImageCard
      exact (pairedRowDifferenceAddHom_range_card_eq_pairedRowMatrix_range_card
        candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference)).symm

/-- Product-form native zero-fiber bound using the full free-image factor `|Rq|^r`. -/
theorem pairedRowZeroFiberCard_mul_rqCard_pow_binaryRank_le_domainCard [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) *
        Fintype.card (RLWE.Rq q (degree + 1)) ^
          (differencePairBinaryTransposeMatrix params
            (leftDifference, rightDifference)).rank ≤
      Fintype.card
        ((Fin (TGSW.rowCount ringRank params.levels) →
            RLWE.Rq q (degree + 1)) ×
          (Fin (TGSW.rowCount ringRank params.levels) →
            RLWE.Rq q (degree + 1))) := by
  calc
    pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) *
        Fintype.card (RLWE.Rq q (degree + 1)) ^
          (differencePairBinaryTransposeMatrix params
            (leftDifference, rightDifference)).rank ≤
      pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) *
        differencePairRowImageCard params candidate
          leftDifference rightDifference :=
        Nat.mul_le_mul_left _
          (rq_card_pow_differencePairBinaryRank_le_rowImageCard
            params heven candidate localParity leftDifference rightDifference)
    _ = _ := pairedRowZeroFiberCard_mul_imageCard_eq_domainCard
      candidate
      (differenceEntryDigits params leftDifference)
      (differenceEntryDigits params rightDifference)

/-- Division form of the free-native-image row zero-fiber estimate. -/
theorem pairedRowZeroFiberCard_le_domainCard_div_rqCard_pow_binaryRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    (pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) : ℝ) ≤
      (Fintype.card
          ((Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1)) ×
            (Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1))) : ℝ) /
        (Fintype.card (RLWE.Rq q (degree + 1)) : ℝ) ^
          (differencePairBinaryTransposeMatrix params
            (leftDifference, rightDifference)).rank := by
  apply (le_div_iff₀ (by positivity :
    (0 : ℝ) < (Fintype.card (RLWE.Rq q (degree + 1)) : ℝ) ^
      (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank)).2
  exact_mod_cast pairedRowZeroFiberCard_mul_rqCard_pow_binaryRank_le_domainCard
    params heven candidate localParity leftDifference rightDifference

/-- Rank-sensitive fixed-pair challenge collision bound retaining the full native free-image
cardinality. -/
theorem differencePairChallengeCollisionCount_le_of_binaryRank_local [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionCount params candidate
        leftDifference rightDifference ≤
      ((Fintype.card
          ((Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1)) ×
            (Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1))) : ℝ) /
        (Fintype.card (RLWE.Rq q (degree + 1)) : ℝ) ^
          (differencePairBinaryTransposeMatrix params
            (leftDifference, rightDifference)).rank) ^ ringRank := by
  unfold differencePairChallengeCollisionCount
  rw [pairedChallengeCollisionCount_eq_rowZeroFiberCard_pow]
  exact pow_le_pow_left₀ (by positivity)
    (pairedRowZeroFiberCard_le_domainCard_div_rqCard_pow_binaryRank
      params heven candidate localParity leftDifference rightDifference) ringRank

/-- Strong local-ring form of the per-pair excess bound. -/
theorem differencePairChallengeCollisionExcess_le_of_binaryRank_local [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionExcess params candidate
        leftDifference rightDifference ≤
      ((Fintype.card
          ((Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1)) ×
            (Fin (TGSW.rowCount ringRank params.levels) →
              RLWE.Rq q (degree + 1))) : ℝ) /
        (Fintype.card (RLWE.Rq q (degree + 1)) : ℝ) ^
          (differencePairBinaryTransposeMatrix params
            (leftDifference, rightDifference)).rank) ^ ringRank -
      Fintype.card (DiagonalChallenge q degree ringRank params.levels) := by
  unfold differencePairChallengeCollisionExcess
  linarith [differencePairChallengeCollisionCount_le_of_binaryRank_local
    params heven candidate localParity leftDifference rightDifference]

/-! ## Rank-weighted global budget -/

/-- Cardinality of the complete paired input space of one native row operator, cast to the
reals for collision accounting. -/
noncomputable def differencePairRowDomainCard [NeZero q]
    (params : Gadget.Base.Parameters q) : ℝ :=
  Fintype.card
    ((Fin (TGSW.rowCount ringRank params.levels) →
        RLWE.Rq q (degree + 1)) ×
      (Fin (TGSW.rowCount ringRank params.levels) →
        RLWE.Rq q (degree + 1)))

/-- Rank-sensitive excess envelope for one ordered difference pair.  Full binary rank is assigned
zero because the local-ring lift proves exact surjectivity.  At deficient rank, the residue-image
cardinality bound replaces the former universal challenge-cardinality square. -/
noncomputable def differencePairBinaryRankCollisionEnvelope [NeZero q]
    (params : Gadget.Base.Parameters q)
    (differences :
      RingGSWCiphertext q (degree + 1) ringRank params.levels ×
        RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  let rank := (differencePairBinaryTransposeMatrix params differences).rank
  if rank = TGSW.rowCount ringRank params.levels then
    0
  else
    (differencePairRowDomainCard
        (degree := degree) (ringRank := ringRank) params /
      (Fintype.card (RLWE.Rq q (degree + 1)) : ℝ) ^ rank) ^ ringRank -
        Fintype.card (DiagonalChallenge q degree ringRank params.levels)

/-- Every ordered pair's native collision excess is bounded by its rank-sensitive envelope when
parity evaluation reflects units. -/
theorem differencePairChallengeCollisionExcess_le_binaryRankEnvelope [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionExcess params candidate
        leftDifference rightDifference ≤
      differencePairBinaryRankCollisionEnvelope params
        (leftDifference, rightDifference) := by
  by_cases hfull :
      (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank =
          TGSW.rowCount ringRank params.levels
  · rw [differencePairChallengeCollisionExcess_eq_zero_of_binaryFullRank
      params heven candidate leftDifference rightDifference localParity hfull]
    simp [differencePairBinaryRankCollisionEnvelope, hfull]
  · simpa [differencePairBinaryRankCollisionEnvelope, hfull,
        differencePairRowDomainCard] using
      (differencePairChallengeCollisionExcess_le_of_binaryRank_local
        params heven candidate localParity leftDifference rightDifference)

/-- Sum of the rank-sensitive envelopes over all ordered native difference pairs. -/
noncomputable def totalDifferencePairBinaryRankCollisionEnvelope [NeZero q]
    (params : Gadget.Base.Parameters q) : ℝ :=
  ∑ leftDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels,
    ∑ rightDifference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      differencePairBinaryRankCollisionEnvelope params
        (leftDifference, rightDifference)

/-- The total native pair excess is bounded by the sum of the rank-sensitive envelopes. -/
theorem totalDifferencePairChallengeCollisionExcess_le_binaryRankEnvelope
    [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree))) :
    totalDifferencePairChallengeCollisionExcess
        (degree := degree) (ringRank := ringRank) params candidate ≤
      totalDifferencePairBinaryRankCollisionEnvelope
        (degree := degree) (ringRank := ringRank) params := by
  unfold totalDifferencePairChallengeCollisionExcess
  unfold totalDifferencePairBinaryRankCollisionEnvelope
  apply Finset.sum_le_sum
  intro leftDifference _
  apply Finset.sum_le_sum
  intro rightDifference _
  exact differencePairChallengeCollisionExcess_le_binaryRankEnvelope
    params heven candidate localParity leftDifference rightDifference

/-- Source-independent normalized collision budget obtained from the complete rank profile of the
binary rectangles rather than only their failure count. -/
noncomputable def binaryRankWeightedDifferencePairCollisionBudget [NeZero q]
    (params : Gadget.Base.Parameters q) : ℝ :=
  totalDifferencePairBinaryRankCollisionEnvelope
      (degree := degree) (ringRank := ringRank) params /
    ((Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
      (Fintype.card
        (DiagonalChallenge q degree ringRank params.levels) : ℝ))

/-- The old global pair budget is bounded by the sharper rank-profile-weighted budget. -/
theorem globalDifferencePairCollisionBudget_le_binaryRankWeighted
    [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree))) :
    globalDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params candidate ≤
      binaryRankWeightedDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params := by
  unfold globalDifferencePairCollisionBudget
  unfold binaryRankWeightedDifferencePairCollisionBudget
  exact div_le_div_of_nonneg_right
    (totalDifferencePairChallengeCollisionExcess_le_binaryRankEnvelope
      params heven candidate localParity) (by positivity)

/-- The exact retained-fiber Pearson expression is controlled by the rank-weighted source-
independent budget. -/
theorem fixedErrorDiagonalNormalizedPairCollisionExcess_le_binaryRankWeighted
    [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalNormalizedPairCollisionExcess
        params candidate sourceError ≤
      binaryRankWeightedDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params :=
  (fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget
    params candidate sourceError).trans
      (globalDifferencePairCollisionBudget_le_binaryRankWeighted
        params heven candidate localParity)

/-- Selected-diagonal replacement bound obtained from the rank-weighted collision budget and the
remaining mixed transformed-error marginal. -/
theorem tvDist_diagonalExperiment_directEntry_le_binaryRankWeighted
    [NeZero q] {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (mixedErrorBound : ℝ)
    (hmixed : ∀ candidate,
      mixedDiagonalErrorDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate ≤ mixedErrorBound) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      Real.sqrt
          (binaryRankWeightedDifferencePairCollisionBudget
            (degree := degree) (ringRank := ringRank) params) /
        2 + mixedErrorBound := by
  apply tvDist_diagonalExperiment_directEntry_le_globalDifferencePairCollisionBudget
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
      (binaryRankWeightedDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params)
      mixedErrorBound
  · intro candidate
    exact globalDifferencePairCollisionBudget_le_binaryRankWeighted
      params heven candidate localParity
  · exact hmixed

/-! ## Premise-free production specialization -/

/-- At production power-of-two coefficient modulus and ring degree, the rank-weighted global
budget applies without a local-homomorphism premise. -/
theorem globalDifferencePairCollisionBudget_le_binaryRankWeighted_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (degreeExponent : ℕ)
    (params : Gadget.Base.Parameters (2 ^ modulusExponent))
    (candidate : Bool) :
    globalDifferencePairCollisionBudget
        (degree := 2 ^ degreeExponent - 1) (ringRank := ringRank)
        params candidate ≤
      binaryRankWeightedDifferencePairCollisionBudget
        (degree := 2 ^ degreeExponent - 1) (ringRank := ringRank) params := by
  have degree_eq : (2 ^ degreeExponent - 1) + 1 = 2 ^ degreeExponent := by
    have degree_positive : 0 < 2 ^ degreeExponent := pow_pos (by omega) degreeExponent
    omega
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  have localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos (2 ^ degreeExponent - 1))) := by
    exact PowerOfTwoLocalRing.rqParityEval_isLocalHom_powerOfTwo_of_degree_eq
      modulusExponent modulusExponent_positive degree_eq
        (Nat.succ_pos (2 ^ degreeExponent - 1))
  exact globalDifferencePairCollisionBudget_le_binaryRankWeighted
    params heven candidate localParity

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
