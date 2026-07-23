/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.RankBound
import FormalProof4FHE.TFHE.NativeDifferenceDigitUniformity
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Binary Obstruction to the Native Diagonal Determinant Route

For an even exact-capacity gadget base, reduction modulo two sends every coefficient digit of the
uniform native difference ciphertext to a fair bit.  Evaluation at `X = 1` then sends every ring
digit independently to a fair bit, so the selected-diagonal row matrix reduces to a uniform square
binary matrix.

This module formalizes that distributional reduction and its consequence: the determinant
non-unit event used by the rank-sharp diagonal certificate has probability at least `1 / 2`.
Thus that event cannot be used as a negligible-loss certificate for the native power-of-two
family.  The result is an obstruction theorem, not a security assumption.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-! ## Balanced even digits -/

/-- Splitting an even-base digit into its quotient by two and its parity bit. -/
def splitEvenDigitEquiv {base halfBase : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2) :
    Fin base ≃ Fin halfBase × ZMod 2 :=
  (Equiv.cast (congrArg Fin hbase)).trans
    (finProdFinEquiv.symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin halfBase)) (ZMod.finEquiv 2).toEquiv))

/-- The bit exposed by `splitEvenDigitEquiv` is the ordinary parity of the natural digit. -/
@[simp]
theorem splitEvenDigitEquiv_snd {base halfBase : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2) (digit : Fin base) :
    (splitEvenDigitEquiv hbase digit).2 = (digit.val : ZMod 2) := by
  subst base
  apply ZMod.val_injective
  change digit.modNat.val = digit.val % 2
  rfl

/-- Parity of the sum of all coefficients in one ring-valued gadget digit. -/
def coefficientDigitParity {base coefficientCount : ℕ}
    (digits : Fin coefficientCount → Fin base) : ZMod 2 :=
  ∑ coefficient, (digits coefficient).val

/-- The information retained beside one coefficient-parity output bit. -/
abbrev EvenCoefficientDigitFiber (halfBase coefficientTail : ℕ) :=
  (Fin (coefficientTail + 1) → Fin halfBase) ×
    (Fin coefficientTail → ZMod 2)

/-- Forward map underlying `evenCoefficientDigitEquiv`. -/
def evenCoefficientDigitEncode {base halfBase coefficientTail : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (digits : Fin (coefficientTail + 1) → Fin base) :
    ZMod 2 × EvenCoefficientDigitFiber halfBase coefficientTail :=
  (coefficientDigitParity digits,
    (fun coefficient => (splitEvenDigitEquiv hbase (digits coefficient)).1,
     fun coefficient => (splitEvenDigitEquiv hbase (digits coefficient.succ)).2))

/-- Inverse map underlying `evenCoefficientDigitEquiv`. -/
def evenCoefficientDigitDecode {base halfBase coefficientTail : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (output : ZMod 2 × EvenCoefficientDigitFiber halfBase coefficientTail) :
    Fin (coefficientTail + 1) → Fin base :=
  fun coefficient =>
    (splitEvenDigitEquiv hbase).symm
      (output.2.1 coefficient,
        Fin.cases (output.1 - ∑ tail, output.2.2 tail) output.2.2 coefficient)

theorem evenCoefficientDigitDecode_encode
    {base halfBase coefficientTail : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (digits : Fin (coefficientTail + 1) → Fin base) :
    evenCoefficientDigitDecode hbase (evenCoefficientDigitEncode hbase digits) = digits := by
  funext coefficient
  apply (splitEvenDigitEquiv hbase).injective
  simp only [evenCoefficientDigitDecode]
  rw [Equiv.apply_symm_apply]
  refine Fin.cases ?_ (fun tail => ?_) coefficient
  · apply Prod.ext
    · rfl
    · simp only [evenCoefficientDigitEncode,
        coefficientDigitParity, Fin.sum_univ_succ, Fin.cases_zero]
      simp_rw [← splitEvenDigitEquiv_snd hbase]
      abel
  · rfl

theorem evenCoefficientDigitEncode_decode
    {base halfBase coefficientTail : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (output : ZMod 2 × EvenCoefficientDigitFiber halfBase coefficientTail) :
    evenCoefficientDigitEncode hbase (evenCoefficientDigitDecode hbase output) = output := by
  rcases output with ⟨total, quotients, tails⟩
  apply Prod.ext
  · simp only [evenCoefficientDigitEncode, coefficientDigitParity]
    simp_rw [← splitEvenDigitEquiv_snd hbase]
    simp only [evenCoefficientDigitDecode, Equiv.apply_symm_apply,
      Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    abel
  · apply Prod.ext
    · funext coefficient
      simp [evenCoefficientDigitEncode, evenCoefficientDigitDecode]
    · funext coefficient
      simp [evenCoefficientDigitEncode, evenCoefficientDigitDecode]

/-- A complete vector of even-base digits is equivalent to its total parity bit together with all
quotients by two and all parity bits except the first. -/
def evenCoefficientDigitEquiv {base halfBase coefficientTail : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2) :
    (Fin (coefficientTail + 1) → Fin base) ≃
      ZMod 2 × EvenCoefficientDigitFiber halfBase coefficientTail where
  toFun := evenCoefficientDigitEncode hbase
  invFun := evenCoefficientDigitDecode hbase
  left_inv := evenCoefficientDigitDecode_encode hbase
  right_inv := evenCoefficientDigitEncode_decode hbase

@[simp]
theorem evenCoefficientDigitEquiv_fst {base halfBase coefficientTail : ℕ}
    [NeZero halfBase] (hbase : base = halfBase * 2)
    (digits : Fin (coefficientTail + 1) → Fin base) :
    (evenCoefficientDigitEquiv hbase digits).1 = coefficientDigitParity digits :=
  rfl

/-! ## Complete digit tensor to binary row matrix -/

/-- The identity-plus-parity matrix obtained from a complete finite coefficient-digit tensor. -/
def binaryRowMatrixOfDigits {base degree ringRank levels : ℕ}
    (digits : Fin (TGSW.rowCount ringRank levels) →
      Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base) :
    Matrix (Fin (TGSW.rowCount ringRank levels))
      (Fin (TGSW.rowCount ringRank levels)) (ZMod 2) :=
  fun row column =>
    let indexed := finProdFinEquiv.symm column
    (if row = column then 1 else 0) +
      coefficientDigitParity (fun coefficient =>
        digits row indexed.1 coefficient indexed.2)

/-- Residual information beside the binary row matrix in the complete digit tensor. -/
abbrev BinaryRowMatrixDigitFiber
    (halfBase degree ringRank levels : ℕ) :=
  Fin (TGSW.rowCount ringRank levels) →
    Fin (ringRank + 1) → Fin levels →
      EvenCoefficientDigitFiber halfBase degree

/-- Forward map underlying `digitTensorBinaryRowMatrixEquiv`. -/
def digitTensorBinaryRowMatrixEncode
    {base halfBase degree ringRank levels : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (digits : Fin (TGSW.rowCount ringRank levels) →
      Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base) :
    Matrix (Fin (TGSW.rowCount ringRank levels))
        (Fin (TGSW.rowCount ringRank levels)) (ZMod 2) ×
      BinaryRowMatrixDigitFiber halfBase degree ringRank levels :=
  (binaryRowMatrixOfDigits digits,
    fun row block level =>
      (evenCoefficientDigitEquiv hbase
        (fun coefficient => digits row block coefficient level)).2)

/-- Inverse map underlying `digitTensorBinaryRowMatrixEquiv`. -/
def digitTensorBinaryRowMatrixDecode
    {base halfBase degree ringRank levels : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (output : Matrix (Fin (TGSW.rowCount ringRank levels))
        (Fin (TGSW.rowCount ringRank levels)) (ZMod 2) ×
      BinaryRowMatrixDigitFiber halfBase degree ringRank levels) :
    Fin (TGSW.rowCount ringRank levels) →
      Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base :=
  fun row block coefficient level =>
    let column := finProdFinEquiv (block, level)
    (evenCoefficientDigitEquiv hbase).symm
      (output.1 row column - (if row = column then 1 else 0),
        output.2 row block level) coefficient

theorem digitTensorBinaryRowMatrixDecode_encode
    {base halfBase degree ringRank levels : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (digits : Fin (TGSW.rowCount ringRank levels) →
      Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base) :
    digitTensorBinaryRowMatrixDecode hbase
      (digitTensorBinaryRowMatrixEncode hbase digits) = digits := by
  funext row block coefficient level
  simp only [digitTensorBinaryRowMatrixDecode, digitTensorBinaryRowMatrixEncode]
  let column := finProdFinEquiv (block, level)
  change (evenCoefficientDigitEquiv hbase).symm
    (binaryRowMatrixOfDigits digits row column -
        (if row = column then 1 else 0),
      (evenCoefficientDigitEquiv hbase
        (fun coefficient => digits row block coefficient level)).2) coefficient = _
  have hmatrix :
      binaryRowMatrixOfDigits digits row column -
          (if row = column then 1 else 0) =
        coefficientDigitParity
          (fun coefficient => digits row block coefficient level) := by
    simp only [binaryRowMatrixOfDigits, column,
      finProdFinEquiv.symm_apply_apply]
    ring
  rw [hmatrix]
  exact congrFun ((evenCoefficientDigitEquiv hbase).symm_apply_apply
    (fun coefficient => digits row block coefficient level)) coefficient

theorem digitTensorBinaryRowMatrixEncode_decode
    {base halfBase degree ringRank levels : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2)
    (output : Matrix (Fin (TGSW.rowCount ringRank levels))
        (Fin (TGSW.rowCount ringRank levels)) (ZMod 2) ×
      BinaryRowMatrixDigitFiber halfBase degree ringRank levels) :
    digitTensorBinaryRowMatrixEncode hbase
      (digitTensorBinaryRowMatrixDecode hbase output) = output := by
  rcases output with ⟨matrix, fiber⟩
  apply Prod.ext
  · funext row column
    let indexed := finProdFinEquiv.symm column
    have hlocal := (evenCoefficientDigitEquiv hbase).apply_symm_apply
      (matrix row column - (if row = column then 1 else 0),
        fiber row indexed.1 indexed.2)
    have hparity := congrArg Prod.fst hlocal
    simp only [evenCoefficientDigitEquiv_fst] at hparity
    simp only [digitTensorBinaryRowMatrixEncode, digitTensorBinaryRowMatrixDecode,
      binaryRowMatrixOfDigits, finProdFinEquiv.apply_symm_apply]
    rw [hparity]
    ring
  · funext row block level
    let column := finProdFinEquiv (block, level)
    have hlocal := (evenCoefficientDigitEquiv hbase).apply_symm_apply
      (matrix row column - (if row = column then 1 else 0),
        fiber row block level)
    simp only [digitTensorBinaryRowMatrixEncode, digitTensorBinaryRowMatrixDecode]
    exact congrArg Prod.snd hlocal

/-- For an even base, the full coefficient-digit tensor is equivalent to its binary row matrix
and an explicit residual fiber. -/
def digitTensorBinaryRowMatrixEquiv
    {base halfBase degree ringRank levels : ℕ} [NeZero halfBase]
    (hbase : base = halfBase * 2) :
    (Fin (TGSW.rowCount ringRank levels) →
      Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base) ≃
      Matrix (Fin (TGSW.rowCount ringRank levels))
          (Fin (TGSW.rowCount ringRank levels)) (ZMod 2) ×
        BinaryRowMatrixDigitFiber halfBase degree ringRank levels where
  toFun := digitTensorBinaryRowMatrixEncode hbase
  invFun := digitTensorBinaryRowMatrixDecode hbase
  left_inv := digitTensorBinaryRowMatrixDecode_encode hbase
  right_inv := digitTensorBinaryRowMatrixEncode_decode hbase

/-- The binary identity-plus-parity row matrix is exactly uniform when the complete even-base
digit tensor is uniform. -/
theorem binaryRowMatrixOfDigits_uniform_evalDist
    {base halfBase degree ringRank levels : ℕ} [NeZero base] [NeZero halfBase]
    (hbase : base = halfBase * 2) :
    evalDist
        (binaryRowMatrixOfDigits <$>
          ($ᵗ (Fin (TGSW.rowCount ringRank levels) →
            Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base))) =
      evalDist
        ($ᵗ Matrix (Fin (TGSW.rowCount ringRank levels))
          (Fin (TGSW.rowCount ringRank levels)) (ZMod 2)) := by
  let equivalence := digitTensorBinaryRowMatrixEquiv
    (degree := degree) (ringRank := ringRank) (levels := levels) hbase
  let Tensor := Fin (TGSW.rowCount ringRank levels) →
    Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base
  let BinaryMatrix := Matrix (Fin (TGSW.rowCount ringRank levels))
    (Fin (TGSW.rowCount ringRank levels)) (ZMod 2)
  let Fiber := BinaryRowMatrixDigitFiber halfBase degree ringRank levels
  have hequivalence :
      evalDist (equivalence <$> ($ᵗ Tensor)) =
        evalDist ($ᵗ (BinaryMatrix × Fiber)) :=
    evalDist_map_bijective_uniform_cross
      (α := Tensor) (β := BinaryMatrix × Fiber)
      equivalence equivalence.bijective
  calc
    evalDist (binaryRowMatrixOfDigits <$> ($ᵗ Tensor)) =
        evalDist (Prod.fst <$> (equivalence <$> ($ᵗ Tensor))) := by
      congr 1
      simp [equivalence, digitTensorBinaryRowMatrixEquiv,
        digitTensorBinaryRowMatrixEncode, Functor.map_map]
    _ = evalDist (Prod.fst <$> ($ᵗ (BinaryMatrix × Fiber))) := by
      rw [evalDist_map, hequivalence, ← evalDist_map]
    _ = evalDist ($ᵗ BinaryMatrix) := evalDist_map_fst_uniformSample_prod

/-! ## Modulo-two evaluation of the negacyclic coefficient ring -/

/-- Reduce polynomial coefficients modulo two and evaluate at `X = 1`. -/
noncomputable def polynomialParityEval {q : ℕ} (heven : 2 ∣ q) :
    Polynomial (ZMod q) →+* ZMod 2 :=
  Polynomial.eval₂RingHom (ZMod.castHom heven (ZMod 2)) 1

/-- The polynomial parity map factors through every negacyclic quotient: `X^n + 1` evaluates to
zero in characteristic two. -/
noncomputable def quotientParityEval {q ringDegree : ℕ} (heven : 2 ∣ q) :
    RLWE.QuotientRq q ringDegree →+* ZMod 2 :=
  Ideal.Quotient.lift _ (polynomialParityEval heven) (by
    intro polynomial hpolynomial
    apply RingHom.mem_ker.mp
    apply (Ideal.span_le.2 ?_) hpolynomial
    intro generator hgenerator
    simp only [Set.mem_singleton_iff] at hgenerator
    subst generator
    apply RingHom.mem_ker.mpr
    simp [polynomialParityEval, LatticeCrypto.negacyclicModulus]
    exact ZMod.natCast_self 2)

/-- Executable ring homomorphism obtained by coefficient reduction modulo two followed by
evaluation at `X = 1`. -/
noncomputable def rqParityEval {q ringDegree : ℕ} (heven : 2 ∣ q)
    (hdegree : 0 < ringDegree) : RLWE.Rq q ringDegree →+* ZMod 2 where
  toFun value := quotientParityEval heven (RLWE.quotientOf hdegree value)
  map_one' := by
    cases ringDegree with
    | zero => omega
    | succ ringDegree =>
        calc
          quotientParityEval heven (RLWE.quotientOf hdegree
              (1 : RLWE.Rq q (ringDegree + 1))) =
              quotientParityEval heven 1 := congrArg _
                ((RLWE.rqSemantics q hdegree).one_sound)
          _ = 1 := map_one (quotientParityEval heven)
  map_zero' := by
    cases ringDegree with
    | zero => omega
    | succ ringDegree =>
        calc
          quotientParityEval heven (RLWE.quotientOf hdegree
              (0 : RLWE.Rq q (ringDegree + 1))) =
              quotientParityEval heven 0 := congrArg _
                (RLWE.quotientOf_zero hdegree)
          _ = 0 := map_zero (quotientParityEval heven)
  map_add' left right := by
    cases ringDegree with
    | zero => omega
    | succ ringDegree =>
        calc
          quotientParityEval heven (RLWE.quotientOf hdegree (left + right)) =
              quotientParityEval heven
                (RLWE.quotientOf hdegree left + RLWE.quotientOf hdegree right) :=
            congrArg _ (RLWE.quotientOf_add hdegree left right)
          _ = _ := map_add (quotientParityEval heven) _ _
  map_mul' left right := by
    cases ringDegree with
    | zero => omega
    | succ ringDegree =>
        calc
          quotientParityEval heven (RLWE.quotientOf hdegree (left * right)) =
              quotientParityEval heven
                (RLWE.quotientOf hdegree left * RLWE.quotientOf hdegree right) :=
            congrArg _ (RLWE.quotientOf_commRing_mul hdegree left right)
          _ = _ := map_mul (quotientParityEval heven) _ _

/-- Coefficient formula for the executable parity-evaluation homomorphism. -/
theorem rqParityEval_apply {q ringDegree : ℕ} (heven : 2 ∣ q)
    (hdegree : 0 < ringDegree) (value : RLWE.Rq q ringDegree) :
    rqParityEval heven hdegree value =
      ∑ coefficient, ZMod.castHom heven (ZMod 2)
        (LatticeCrypto.Poly.toPi value coefficient) := by
  change quotientParityEval heven
      (LatticeCrypto.NegacyclicQuotient.ofBackend
        (LatticeCrypto.vectorBackend (ZMod q) ringDegree) value) = _
  unfold quotientParityEval LatticeCrypto.NegacyclicQuotient.ofBackend
    LatticeCrypto.NegacyclicQuotient.ofPolynomial
  rw [Ideal.Quotient.lift_mk]
  simp [polynomialParityEval, LatticeCrypto.PolyBackend.toPolynomial,
    LatticeCrypto.Poly.toPi]
  rfl

/-- Parity evaluation of one executable ring digit is the parity sum of its complete finite
coefficient-digit vector. -/
theorem rqParityEval_ringDigit [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (value : RLWE.Rq q (degree + 1)) (level : Fin params.levels) :
    rqParityEval heven (Nat.succ_pos degree)
        (Gadget.Base.ringDigit params value level) =
      coefficientDigitParity (fun coefficient =>
        Gadget.Base.ringCoefficientDigitVector params value coefficient level) := by
  rw [rqParityEval_apply]
  unfold coefficientDigitParity
  apply Finset.sum_congr rfl
  intro coefficient _
  rw [← Gadget.Base.ringCoefficientDigitVector_cast
    params value coefficient level]
  simp

/-! ## Native difference lift -/

/-- Binary identity-plus-parity matrix extracted from the complete native difference
ciphertext. -/
def differenceBinaryRowMatrix [NeZero q]
    (params : Gadget.Base.Parameters q)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    Matrix (Fin (TGSW.rowCount ringRank params.levels))
      (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2) :=
  binaryRowMatrixOfDigits (differenceDigitCoefficientVector params difference)

/-- Mapping the native identity-plus-ring-digit row matrix through parity evaluation gives the
explicit binary row matrix extracted from the complete finite digit tensor.  The candidate sign
disappears in characteristic two. -/
theorem rqParityEval_mapMatrix_rowMatrix_difference [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    (rqParityEval heven (Nat.succ_pos degree)).mapMatrix
        (rowMatrix candidate (differenceEntryDigits params difference)) =
      differenceBinaryRowMatrix params difference := by
  classical
  ext row column
  let indexed := finProdFinEquiv.symm column
  change rqParityEval heven (Nat.succ_pos degree)
      (rowMatrix candidate (differenceEntryDigits params difference) row column) = _
  rw [rowMatrix_apply, map_add, map_mul]
  unfold differenceEntryDigits Gadget.Base.ringExtendedDigits
  rw [rqParityEval_ringDigit]
  unfold differenceBinaryRowMatrix binaryRowMatrixOfDigits
  dsimp only
  have hdiag : rqParityEval heven (Nat.succ_pos degree)
      (if row = column then 1 else 0) =
        (if row = column then 1 else 0) := by
    split_ifs <;> simp
  rw [hdiag]
  unfold differenceDigitCoefficientVector
  cases candidate <;> simp [signedValue]

/-- Rank failure of the reduced binary matrix forces determinant non-unitness over the original
power-of-two coefficient ring.  Only preservation of units by the parity-evaluation ring hom is
used; no local-ring converse is required. -/
theorem binaryRankFailure_implies_determinantFailure [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hfailure : (differenceBinaryRowMatrix params difference).rank <
      TGSW.rowCount ringRank params.levels) :
    DiagonalRowDeterminantFailure params candidate difference := by
  unfold DiagonalRowDeterminantFailure
  intro hunit
  have hmappedUnit : IsUnit
      (rqParityEval heven (Nat.succ_pos degree)
        (rowMatrix candidate (differenceEntryDigits params difference)).det) :=
    hunit.map (rqParityEval heven (Nat.succ_pos degree))
  have hmappedDet :
      rqParityEval heven (Nat.succ_pos degree)
          (rowMatrix candidate (differenceEntryDigits params difference)).det =
        (differenceBinaryRowMatrix params difference).det := by
    rw [RingHom.map_det, rqParityEval_mapMatrix_rowMatrix_difference]
  have hbinaryDet : IsUnit (differenceBinaryRowMatrix params difference).det := by
    rw [← hmappedDet]
    exact hmappedUnit
  have hbinaryMatrix : IsUnit (differenceBinaryRowMatrix params difference) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hbinaryDet
  have hrank := Matrix.rank_of_isUnit
    (differenceBinaryRowMatrix params difference) hbinaryMatrix
  have hrankFull : (differenceBinaryRowMatrix params difference).rank =
      TGSW.rowCount ringRank params.levels := by
    simpa using hrank
  omega

/-! ## Constant binary rank-failure probability -/

/-- A uniform nonempty square binary matrix fails to have full rank with probability at least
`1 / 2`.  This is the last-factor consequence of the exact finite-field rank formula. -/
theorem one_half_le_binarySquareRankFailure_toReal
    (dimension : ℕ) (hdimension : 0 < dimension) :
    (1 : ℝ) / 2 ≤
      (Pr[(fun matrix : Matrix (Fin dimension) (Fin dimension) (ZMod 2) =>
          matrix.rank < dimension) |
        ($ᵗ Matrix (Fin dimension) (Fin dimension) (ZMod 2))]).toReal := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hdimension)
  simp only [Nat.succ_eq_add_one]
  rw [FormalProof4FHE.FiniteFieldRank.rankFailure_toReal_eq
    (F := ZMod 2) (tail + 1) (tail + 1) le_rfl]
  change (1 : ℝ) / 2 ≤ 1 -
    ∏ index : Fin (tail + 1),
      (1 - (2 : ℝ) ^ index.val / (2 : ℝ) ^ (tail + 1))
  rw [Fin.prod_univ_castSucc]
  have hfactor_nonneg (index : Fin tail) :
      0 ≤ 1 - (2 : ℝ) ^ index.castSucc.val / (2 : ℝ) ^ (tail + 1) := by
    have hpow : (2 : ℝ) ^ index.castSucc.val ≤ (2 : ℝ) ^ (tail + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hdenom : 0 < (2 : ℝ) ^ (tail + 1) := by positivity
    exact sub_nonneg.mpr ((div_le_one hdenom).2 hpow)
  have hfactor_le_one (index : Fin tail) :
      1 - (2 : ℝ) ^ index.castSucc.val / (2 : ℝ) ^ (tail + 1) ≤ 1 := by
    have hratio : 0 ≤ (2 : ℝ) ^ index.castSucc.val /
        (2 : ℝ) ^ (tail + 1) := by positivity
    linarith
  have hproduct_nonneg :
      0 ≤ ∏ index : Fin tail,
        (1 - (2 : ℝ) ^ index.castSucc.val / (2 : ℝ) ^ (tail + 1)) :=
    Finset.prod_nonneg fun index _ => hfactor_nonneg index
  have hproduct_le_one :
      (∏ index : Fin tail,
        (1 - (2 : ℝ) ^ index.castSucc.val / (2 : ℝ) ^ (tail + 1))) ≤ 1 :=
    Finset.prod_le_one
      (fun index _ => hfactor_nonneg index)
      (fun index _ => hfactor_le_one index)
  have hlast :
      1 - (2 : ℝ) ^ (Fin.last tail).val / (2 : ℝ) ^ (tail + 1) =
        (1 : ℝ) / 2 := by
    simp only [Fin.val_last, pow_succ]
    have hpow : (2 : ℝ) ^ tail ≠ 0 := by positivity
    field_simp
    norm_num
  rw [hlast]
  nlinarith

/-- At exact gadget capacity with an even base, the binary row matrix extracted from a uniform
native difference ciphertext is exactly a uniform square binary matrix. -/
theorem differenceBinaryRowMatrix_uniform_evalDist [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) [NeZero halfBase]
    (hbase : params.base = halfBase * 2) :
    evalDist
        (differenceBinaryRowMatrix params <$>
          ($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels)) =
      evalDist
        ($ᵗ Matrix (Fin (TGSW.rowCount ringRank params.levels))
          (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2)) := by
  let Difference := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Tensor := Fin (TGSW.rowCount ringRank params.levels) →
    Fin (ringRank + 1) → Fin (degree + 1) →
      Fin params.levels → Fin params.base
  let BinaryMatrix := Matrix (Fin (TGSW.rowCount ringRank params.levels))
    (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2)
  have hdigits :
      evalDist
          (differenceDigitCoefficientVector params <$> ($ᵗ Difference)) =
        evalDist ($ᵗ Tensor) :=
    differenceDigitCoefficientVector_uniform_evalDist params hcapacity
  have hbinary :
      evalDist (binaryRowMatrixOfDigits <$> ($ᵗ Tensor)) =
        evalDist ($ᵗ BinaryMatrix) :=
    binaryRowMatrixOfDigits_uniform_evalDist hbase
  calc
    evalDist (differenceBinaryRowMatrix params <$> ($ᵗ Difference)) =
        evalDist (binaryRowMatrixOfDigits <$>
          (differenceDigitCoefficientVector params <$> ($ᵗ Difference))) := by
      congr 1
      change ((fun difference : Difference =>
        binaryRowMatrixOfDigits
          (differenceDigitCoefficientVector params difference)) <$>
            ($ᵗ Difference)) = _
      rw [Functor.map_map]
    _ = evalDist (binaryRowMatrixOfDigits <$> ($ᵗ Tensor)) := by
      rw [evalDist_map, hdigits, ← evalDist_map]
    _ = evalDist ($ᵗ BinaryMatrix) := hbinary

/-- Exact capacity, a positive level count, and an even base force the coefficient modulus to be
even. -/
theorem modulus_even_of_exactCapacity_evenBase [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) (hbase : params.base = halfBase * 2)
    (hlevels : 0 < params.levels) : 2 ∣ q := by
  rw [hcapacity, hbase]
  obtain ⟨levelTail, hlevel⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hlevels)
  rw [hlevel, pow_succ]
  refine ⟨(halfBase * 2) ^ levelTail * halfBase, ?_⟩
  ring

/-- **Native determinant obstruction.**  At exact capacity with a positive number of levels and
an even base, the determinant non-unit probability is at least `1 / 2` for either candidate bit.
Hence the rank-sharp determinant route cannot supply a negligible selected-diagonal loss for this
native parameter regime. -/
theorem one_half_le_diagonalRowDeterminantFailureProbability [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) [NeZero halfBase]
    (hbase : params.base = halfBase * 2)
    (hlevels : 0 < params.levels) (candidate : Bool) :
    (1 : ℝ) / 2 ≤
      diagonalRowDeterminantFailureProbability
        (degree := degree) (ringRank := ringRank) params candidate := by
  let dimension := TGSW.rowCount ringRank params.levels
  let Difference := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let BinaryMatrix := Matrix (Fin dimension) (Fin dimension) (ZMod 2)
  have hdimension : 0 < dimension := by
    unfold dimension TGSW.rowCount
    exact Nat.mul_pos (Nat.succ_pos ringRank) hlevels
  have heven : 2 ∣ q :=
    modulus_even_of_exactCapacity_evenBase params hcapacity halfBase hbase hlevels
  have hdist :
      evalDist
          (differenceBinaryRowMatrix params <$> ($ᵗ Difference)) =
        evalDist ($ᵗ BinaryMatrix) :=
    differenceBinaryRowMatrix_uniform_evalDist params hcapacity halfBase hbase
  have hmappedProbability :
      Pr[(fun matrix : BinaryMatrix => matrix.rank < dimension) |
          differenceBinaryRowMatrix params <$> ($ᵗ Difference)] =
        Pr[(fun matrix : BinaryMatrix => matrix.rank < dimension) |
          ($ᵗ BinaryMatrix)] :=
    probEvent_congr' (fun _ _ => Iff.rfl) hdist
  have hmapProbability :
      Pr[(fun matrix : BinaryMatrix => matrix.rank < dimension) |
          differenceBinaryRowMatrix params <$> ($ᵗ Difference)] =
        Pr[(fun difference : Difference =>
            (differenceBinaryRowMatrix params difference).rank < dimension) |
          ($ᵗ Difference)] := by
    calc
      _ = Pr[((fun matrix : BinaryMatrix => matrix.rank < dimension) ∘
          differenceBinaryRowMatrix params) | ($ᵗ Difference)] :=
        probEvent_map ($ᵗ Difference) (differenceBinaryRowMatrix params)
          (fun matrix : BinaryMatrix => matrix.rank < dimension)
      _ = _ := by
        congr 1
  have hprobabilityMono :
      Pr[(fun difference : Difference =>
          (differenceBinaryRowMatrix params difference).rank < dimension) |
        ($ᵗ Difference)] ≤
      Pr[DiagonalRowDeterminantFailure params candidate | ($ᵗ Difference)] := by
    apply probEvent_mono
    intro difference _ hfailure
    exact binaryRankFailure_implies_determinantFailure
      params heven candidate difference hfailure
  calc
    (1 : ℝ) / 2 ≤
        (Pr[(fun matrix : BinaryMatrix => matrix.rank < dimension) |
          ($ᵗ BinaryMatrix)]).toReal :=
      one_half_le_binarySquareRankFailure_toReal dimension hdimension
    _ = (Pr[(fun matrix : BinaryMatrix => matrix.rank < dimension) |
          differenceBinaryRowMatrix params <$> ($ᵗ Difference)]).toReal :=
      congrArg ENNReal.toReal hmappedProbability.symm
    _ = (Pr[(fun difference : Difference =>
          (differenceBinaryRowMatrix params difference).rank < dimension) |
        ($ᵗ Difference)]).toReal := congrArg ENNReal.toReal hmapProbability
    _ ≤ (Pr[DiagonalRowDeterminantFailure params candidate |
        ($ᵗ Difference)]).toReal :=
      (ENNReal.toReal_le_toReal probEvent_ne_top probEvent_ne_top).2
        hprobabilityMono
    _ = diagonalRowDeterminantFailureProbability
        (degree := degree) (ringRank := ringRank) params candidate := rfl

/-- The exact rank-sharp selected-diagonal loss itself is at least `1 / 2` in the same native
even-base regime, independently of the source and target error samplers. -/
theorem one_half_le_rankSharpDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) [NeZero halfBase]
    (hbase : params.base = halfBase * 2)
    (hlevels : 0 < params.levels)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    (1 : ℝ) / 2 ≤
      rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate := by
  rw [rankSharpDiagonalOperatorLoss_eq_determinantFailure_add_mixedError]
  exact (one_half_le_diagonalRowDeterminantFailureProbability
    params hcapacity halfBase hbase hlevels candidate).trans
      (le_add_of_nonneg_right
        (mixedDiagonalErrorDistance_nonneg (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler candidate))

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
