/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.ParallelBatch
import FormalProof4FHE.RLWE.Security
import FormalProof4FHE.TFHE.CoefficientStructuredLWE
import Mathlib.RingTheory.AdjoinRoot

/-!
# Even/Odd Decomposition of Power-of-Two Negacyclic RLWE

This file decomposes

`ZMod q[X] / (X^(2*n) + 1)`

as two coefficient copies of `ZMod q[Y] / (Y^n + 1)`, with `Y = X^2`.  The decomposition is
additive rather than a product-ring equivalence.  Its multiplication law is the quadratic tower

`(a0 + X*a1) * (b0 + X*b1) = (a0*b0 + Y*a1*b1) + X*(a0*b1 + a1*b0)`.

The security application uses only multiplication by an odd-coordinate secret `X*z(Y)`.  One
degree-`2*n` sample then becomes two ordinary degree-`n` RLWE samples under the same secret.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.EvenOddDecomposition

noncomputable section

open TFHE.Native.CoefficientStructuredLWE

/-! ## Coefficient splitting -/

/-- Interleaved parity coordinates: `(0,i)` is coefficient `2*i`, and `(1,i)` is `2*i+1`. -/
def parityIndexEquiv (half : ℕ) : Fin 2 × Fin half ≃ Fin (2 * half) :=
  (Equiv.prodComm (Fin 2) (Fin half)).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm half 2)))

@[simp]
theorem parityIndexEquiv_even (half : ℕ) (index : Fin half) :
    (parityIndexEquiv half (0, index)).val = 2 * index.val := by
  simp [parityIndexEquiv, finProdFinEquiv]

@[simp]
theorem parityIndexEquiv_odd (half : ℕ) (index : Fin half) :
    (parityIndexEquiv half (1, index)).val = 2 * index.val + 1 := by
  simp [parityIndexEquiv, finProdFinEquiv]
  omega

/-- Split an interleaved coefficient vector into its even and odd subsequences. -/
def coefficientParityEquiv (R : Type) (half : ℕ) :
    (Fin (2 * half) → R) ≃ ((Fin half → R) × (Fin half → R)) :=
  ((parityIndexEquiv half).piCongrLeft (fun _ ↦ R)).symm |>.trans
    (Equiv.curry (Fin 2) (Fin half) R) |>.trans
    (finTwoArrowEquiv (Fin half → R))

@[simp]
theorem coefficientParityEquiv_apply_even
    (R : Type) (half : ℕ) (value : Fin (2 * half) → R) (index : Fin half) :
    (coefficientParityEquiv R half value).1 index =
      value (parityIndexEquiv half (0, index)) := by
  rfl

@[simp]
theorem coefficientParityEquiv_apply_odd
    (R : Type) (half : ℕ) (value : Fin (2 * half) → R) (index : Fin half) :
    (coefficientParityEquiv R half value).2 index =
      value (parityIndexEquiv half (1, index)) := by
  rfl

@[simp]
theorem coefficientParityEquiv_symm_even
    (R : Type) (half : ℕ) (value : (Fin half → R) × (Fin half → R))
    (index : Fin half) :
    (coefficientParityEquiv R half).symm value (parityIndexEquiv half (0, index)) =
      value.1 index := by
  simp [coefficientParityEquiv]

@[simp]
theorem coefficientParityEquiv_symm_odd
    (R : Type) (half : ℕ) (value : (Fin half → R) × (Fin half → R))
    (index : Fin half) :
    (coefficientParityEquiv R half).symm value (parityIndexEquiv half (1, index)) =
      value.2 index := by
  simp [coefficientParityEquiv]

/-! ## Executable ring splitting -/

/-- The executable degree-`2 * half` carrier, split into its even and odd coefficient
polynomials of degree `half`.  This is an additive-coordinate equivalence, not a ring-product
equivalence. -/
def ringParityEquiv (q half : ℕ) :
    RLWE.Rq q (2 * half) ≃ (RLWE.Rq q half × RLWE.Rq q half) :=
  (coefficientEquiv q (2 * half)).trans
    ((coefficientParityEquiv (ZMod q) half).trans
      ((coefficientEquiv q half).symm.prodCongr
        (coefficientEquiv q half).symm))

/-- Interleave two smaller executable polynomials as the even and odd coefficients of a
degree-`2 * half` polynomial. -/
def joinRq (q half : ℕ) (even odd : RLWE.Rq q half) : RLWE.Rq q (2 * half) :=
  (ringParityEquiv q half).symm (even, odd)

@[simp]
theorem ringParityEquiv_joinRq (q half : ℕ)
    (even odd : RLWE.Rq q half) :
    ringParityEquiv q half (joinRq q half even odd) = (even, odd) :=
  (ringParityEquiv q half).apply_symm_apply (even, odd)

@[simp]
theorem joinRq_ringParityEquiv (q half : ℕ)
    (value : RLWE.Rq q (2 * half)) :
    joinRq q half (ringParityEquiv q half value).1
        (ringParityEquiv q half value).2 = value := by
  exact (ringParityEquiv q half).symm_apply_apply value

@[simp]
theorem coefficientParityEquiv_joinRq (q half : ℕ)
    (even odd : RLWE.Rq q half) :
    coefficientParityEquiv (ZMod q) half
        (coefficientEquiv q (2 * half) (joinRq q half even odd)) =
      (coefficientEquiv q half even, coefficientEquiv q half odd) := by
  let reconstruction := (coefficientEquiv q half).symm.prodCongr
    (coefficientEquiv q half).symm
  apply reconstruction.injective
  change ringParityEquiv q half (joinRq q half even odd) =
    reconstruction (coefficientEquiv q half even, coefficientEquiv q half odd)
  rw [ringParityEquiv_joinRq]
  simp [reconstruction]

@[simp]
theorem coefficientEquiv_joinRq_even (q half : ℕ)
    (even odd : RLWE.Rq q half) (index : Fin half) :
    coefficientEquiv q (2 * half) (joinRq q half even odd)
        (parityIndexEquiv half (0, index)) =
      coefficientEquiv q half even index := by
  have equality := congrArg Prod.fst
    (coefficientParityEquiv_joinRq q half even odd)
  exact congrFun equality index

@[simp]
theorem coefficientEquiv_joinRq_odd (q half : ℕ)
    (even odd : RLWE.Rq q half) (index : Fin half) :
    coefficientEquiv q (2 * half) (joinRq q half even odd)
        (parityIndexEquiv half (1, index)) =
      coefficientEquiv q half odd index := by
  have equality := congrArg Prod.snd
    (coefficientParityEquiv_joinRq q half even odd)
  exact congrFun equality index

/-- The degree-bounded polynomial represented by a coefficient vector. -/
noncomputable def coefficientPolynomial {q degree : ℕ}
    (value : Coefficients q degree) : Polynomial (ZMod q) :=
  ∑ index : Fin degree, Polynomial.monomial index.val (value index)

/-- `quotientOf` is the quotient class of the explicit coefficient polynomial. -/
theorem quotientOf_eq_ofPolynomial_coefficients {q degree : ℕ}
    (hdegree : 0 < degree) (value : RLWE.Rq q degree) :
    RLWE.quotientOf hdegree value =
      LatticeCrypto.NegacyclicQuotient.ofPolynomial degree
        (coefficientPolynomial (coefficientEquiv q degree value)) := by
  rfl

/-- The polynomial of an interleaving is the sum of its even and odd monomials. -/
theorem coefficientPolynomial_joinRq (q half : ℕ)
    (even odd : RLWE.Rq q half) :
    coefficientPolynomial
        (coefficientEquiv q (2 * half) (joinRq q half even odd)) =
      (∑ index : Fin half,
        Polynomial.monomial (2 * index.val) (coefficientEquiv q half even index)) +
      ∑ index : Fin half,
        Polynomial.monomial (2 * index.val + 1)
          (coefficientEquiv q half odd index) := by
  unfold coefficientPolynomial
  rw [← (parityIndexEquiv half).sum_comp, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  simp only [parityIndexEquiv_even, parityIndexEquiv_odd,
    coefficientEquiv_joinRq_even, coefficientEquiv_joinRq_odd]

/-! ## Semantic quadratic-tower embedding -/

/-- The root `X` of the degree-`2 * half` negacyclic quotient. -/
noncomputable def largeRoot (q half : ℕ) : RLWE.QuotientRq q (2 * half) :=
  AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half))

/-- Embed the degree-`half` negacyclic quotient into the degree-`2 * half` quotient by
sending its formal root `Y` to `X²`. -/
noncomputable def evenQuotientHom (q half : ℕ) :
    RLWE.QuotientRq q half →+* RLWE.QuotientRq q (2 * half) :=
  AdjoinRoot.lift
    (AdjoinRoot.of (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)))
    (largeRoot q half ^ 2)
    (by
      simp only [LatticeCrypto.negacyclicModulus, Polynomial.eval₂_add,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
      calc
        (largeRoot q half ^ 2) ^ half + 1 =
            largeRoot q half ^ (2 * half) + 1 := by rw [pow_mul]
        _ = (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)).eval₂
            (AdjoinRoot.of (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)))
            (largeRoot q half) := by
              simp [LatticeCrypto.negacyclicModulus]
              rfl
        _ = 0 := AdjoinRoot.eval₂_root _)

@[simp]
theorem evenQuotientHom_root (q half : ℕ) :
    evenQuotientHom q half
        (AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half)) =
      largeRoot q half ^ 2 := by
  unfold evenQuotientHom
  exact AdjoinRoot.lift_root _

/-- Evaluating a degree-`half` coefficient polynomial at `X²` is its even-coordinate
embedding in the large quotient. -/
theorem eval₂_coefficientPolynomial_largeRoot_sq (q half : ℕ)
    (value : Coefficients q half) :
    (coefficientPolynomial value).eval₂
        (AdjoinRoot.of (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)))
        (largeRoot q half ^ 2) =
      LatticeCrypto.NegacyclicQuotient.ofPolynomial (2 * half)
        (∑ index : Fin half,
          Polynomial.monomial (2 * index.val) (value index)) := by
  unfold largeRoot
  rw [show coefficientPolynomial value =
      ∑ index : Fin half, Polynomial.monomial index.val (value index) by rfl]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  change (∑ index : Fin half,
      AdjoinRoot.of (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half))
          (value index) *
            (AdjoinRoot.root
              (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)) ^ 2) ^ index.val) = _
  rw [show (∑ index : Fin half,
      AdjoinRoot.of (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half))
          (value index) *
            (AdjoinRoot.root
              (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)) ^ 2) ^ index.val) =
      ∑ index : Fin half,
        AdjoinRoot.of (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half))
          (value index) *
            AdjoinRoot.root
              (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)) ^
                (2 * index.val) by
    apply Finset.sum_congr rfl
    intro index _
    rw [pow_mul]]
  unfold LatticeCrypto.NegacyclicQuotient.ofPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  rfl

/-- The semantic embedding is exactly executable placement in the even coefficients. -/
theorem evenQuotientHom_quotientOf (q half : ℕ) (hhalf : 0 < half)
    (value : RLWE.Rq q half) :
    evenQuotientHom q half (RLWE.quotientOf hhalf value) =
      RLWE.quotientOf (by omega : 0 < 2 * half)
        (joinRq q half value 0) := by
  rw [quotientOf_eq_ofPolynomial_coefficients hhalf,
    quotientOf_eq_ofPolynomial_coefficients (by omega : 0 < 2 * half)]
  change (AdjoinRoot.lift
      (AdjoinRoot.of (LatticeCrypto.negacyclicModulus (ZMod q) (2 * half)))
      (largeRoot q half ^ 2) _)
        (AdjoinRoot.mk (LatticeCrypto.negacyclicModulus (ZMod q) half)
          (coefficientPolynomial (coefficientEquiv q half value))) = _
  rw [AdjoinRoot.lift_mk]
  rw [coefficientPolynomial_joinRq]
  simp only [coefficientEquiv_zero, Pi.zero_apply, Polynomial.monomial_zero_right,
    Finset.sum_const_zero, add_zero]
  exact eval₂_coefficientPolynomial_largeRoot_sq q half
    (coefficientEquiv q half value)

/-- Odd-coordinate placement is `X` times the embedded small polynomial. -/
theorem quotientOf_joinRq_zero (q half : ℕ) (hhalf : 0 < half)
    (value : RLWE.Rq q half) :
    RLWE.quotientOf (by omega : 0 < 2 * half)
        (joinRq q half 0 value) =
      largeRoot q half *
        evenQuotientHom q half (RLWE.quotientOf hhalf value) := by
  rw [evenQuotientHom_quotientOf q half hhalf]
  rw [quotientOf_eq_ofPolynomial_coefficients (by omega : 0 < 2 * half),
    quotientOf_eq_ofPolynomial_coefficients (by omega : 0 < 2 * half)]
  rw [coefficientPolynomial_joinRq, coefficientPolynomial_joinRq]
  simp only [coefficientEquiv_zero, Pi.zero_apply, Polynomial.monomial_zero_right,
    Finset.sum_const_zero, zero_add, add_zero]
  unfold largeRoot LatticeCrypto.NegacyclicQuotient.ofPolynomial
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  change (Ideal.Quotient.mk _)
      (Polynomial.monomial (2 * index.val + 1)
        (coefficientEquiv q half value index)) =
    (Ideal.Quotient.mk _) Polynomial.X *
      (Ideal.Quotient.mk _)
        (Polynomial.monomial (2 * index.val)
          (coefficientEquiv q half value index))
  rw [← map_mul, Polynomial.X_mul_monomial]

/-! ## Executable tower multiplication -/

/-- The executable representative of the small quotient's formal root `Y`. -/
noncomputable def smallRootRq (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) : RLWE.Rq q half :=
  (RLWE.quotientEquiv hhalf).symm
    (AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half))

@[simp]
theorem quotientOf_smallRootRq (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) :
    RLWE.quotientOf hhalf (smallRootRq q half hhalf) =
      AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half) := by
  change RLWE.quotientEquiv hhalf
      ((RLWE.quotientEquiv hhalf).symm
        (AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half))) = _
  exact (RLWE.quotientEquiv hhalf).apply_symm_apply _

/-- Splitting and rejoining is additive in the two coefficient components. -/
theorem joinRq_add_decomposition (q half : ℕ)
    (even odd : RLWE.Rq q half) :
    joinRq q half even odd =
      joinRq q half even 0 + joinRq q half 0 odd := by
  apply (coefficientEquiv q (2 * half)).injective
  funext coefficient
  obtain ⟨⟨parity, index⟩, rfl⟩ := (parityIndexEquiv half).surjective coefficient
  rw [coefficientEquiv_add]
  fin_cases parity <;> simp

/-- Interleaving preserves componentwise addition. -/
theorem joinRq_add (q half : ℕ)
    (even₁ odd₁ even₂ odd₂ : RLWE.Rq q half) :
    joinRq q half (even₁ + even₂) (odd₁ + odd₂) =
      joinRq q half even₁ odd₁ + joinRq q half even₂ odd₂ := by
  apply (coefficientEquiv q (2 * half)).injective
  funext coefficient
  obtain ⟨⟨parity, index⟩, rfl⟩ := (parityIndexEquiv half).surjective coefficient
  rw [coefficientEquiv_add]
  fin_cases parity <;> simp

/-- Semantic form of the executable even/odd decomposition. -/
theorem quotientOf_joinRq (q half : ℕ) (hhalf : 0 < half)
    (even odd : RLWE.Rq q half) :
    RLWE.quotientOf (by omega : 0 < 2 * half) (joinRq q half even odd) =
      evenQuotientHom q half (RLWE.quotientOf hhalf even) +
        largeRoot q half *
          evenQuotientHom q half (RLWE.quotientOf hhalf odd) := by
  rw [joinRq_add_decomposition, RLWE.quotientOf_add,
    ← evenQuotientHom_quotientOf q half hhalf,
    quotientOf_joinRq_zero q half hhalf]

/-- Multiplication by an odd-coordinate secret is exactly two small-ring products.  The even
component has the public unit twist `Y`; the odd component is untwisted. -/
theorem joinRq_mul_odd (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (maskEven maskOdd secret : RLWE.Rq q half) :
    joinRq q half maskEven maskOdd * joinRq q half 0 secret =
      joinRq q half
        (smallRootRq q half hhalf * maskOdd * secret)
        (maskEven * secret) := by
  cases half with
  | zero => omega
  | succ half =>
      apply RLWE.quotientOf_injective (q := q) (by omega : 0 < 2 * (half + 1))
      change RLWE.quotientOf _
          ((RLWE.negacyclicRing q (2 * (half + 1))).mul
            (joinRq q (half + 1) maskEven maskOdd)
            (joinRq q (half + 1) 0 secret)) =
        RLWE.quotientOf _
          (joinRq q (half + 1)
            ((RLWE.negacyclicRing q (half + 1)).mul
              ((RLWE.negacyclicRing q (half + 1)).mul
                (smallRootRq q (half + 1) hhalf) maskOdd) secret)
            ((RLWE.negacyclicRing q (half + 1)).mul maskEven secret))
      rw [RLWE.quotientOf_mul]
      rw [quotientOf_joinRq q (half + 1) hhalf,
        quotientOf_joinRq q (half + 1) hhalf,
        quotientOf_joinRq q (half + 1) hhalf]
      simp only [RLWE.quotientOf_zero, map_zero, zero_add]
      simp_rw [RLWE.quotientOf_mul]
      simp only [map_mul, quotientOf_smallRootRq, evenQuotientHom_root]
      ring

/-- The same identity for the proof-facing `CommRing` multiplication used by matrix LWE. -/
theorem joinRq_commRing_mul_odd (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (maskEven maskOdd secret : RLWE.Rq q half) :
    @Mul.mul (RLWE.Rq q (2 * half))
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) (2 * half)).toMul
        (joinRq q half maskEven maskOdd) (joinRq q half 0 secret) =
      joinRq q half
        (@Mul.mul (RLWE.Rq q half)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) half).toMul
          (@Mul.mul (RLWE.Rq q half)
            (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) half).toMul
            (smallRootRq q half hhalf) maskOdd) secret)
        (@Mul.mul (RLWE.Rq q half)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) half).toMul
          maskEven secret) := by
  apply RLWE.quotientOf_injective (q := q) (by omega : 0 < 2 * half)
  rw [RLWE.quotientOf_commRing_mul]
  rw [quotientOf_joinRq q half hhalf,
    quotientOf_joinRq q half hhalf,
    quotientOf_joinRq q half hhalf]
  simp only [RLWE.quotientOf_zero, map_zero, zero_add]
  simp_rw [RLWE.quotientOf_commRing_mul]
  simp only [map_mul, quotientOf_smallRootRq, evenQuotientHom_root]
  ring

/-! ## The public `Y`-twist is a permutation -/

/-- The proof-facing multiplication operation used by the generic matrix-LWE interface. -/
noncomputable def proofMul (q degree : ℕ)
    (left right : RLWE.Rq q degree) : RLWE.Rq q degree :=
  @Mul.mul (RLWE.Rq q degree)
    (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toMul
    left right

/-- Executable representative of `-Y^(half - 1)`, the inverse of `Y` in
`ZMod q[Y] / (Y^half + 1)`. -/
noncomputable def smallRootInverseRq (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) : RLWE.Rq q half :=
  (RLWE.quotientEquiv hhalf).symm
    (-(AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half) ^ (half - 1)))

@[simp]
theorem quotientOf_smallRootInverseRq (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) :
    RLWE.quotientOf hhalf (smallRootInverseRq q half hhalf) =
      -(AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half) ^ (half - 1)) := by
  change RLWE.quotientEquiv hhalf
      ((RLWE.quotientEquiv hhalf).symm
        (-(AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half) ^
          (half - 1)))) = _
  exact (RLWE.quotientEquiv hhalf).apply_symm_apply _

/-- Multiply by the public small-ring root `Y`. -/
noncomputable def rootTwist (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (value : RLWE.Rq q half) : RLWE.Rq q half :=
  proofMul q half (smallRootRq q half hhalf) value

/-- Multiply by `Y⁻¹ = -Y^(half - 1)`. -/
noncomputable def rootUntwist (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (value : RLWE.Rq q half) : RLWE.Rq q half :=
  proofMul q half (smallRootInverseRq q half hhalf) value

@[simp]
theorem rootUntwist_rootTwist (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (value : RLWE.Rq q half) :
    rootUntwist q half hhalf (rootTwist q half hhalf value) = value := by
  apply RLWE.quotientOf_injective (q := q) hhalf
  unfold rootUntwist rootTwist
  unfold proofMul
  rw [RLWE.quotientOf_commRing_mul, RLWE.quotientOf_commRing_mul,
    quotientOf_smallRootInverseRq, quotientOf_smallRootRq]
  let root : RLWE.QuotientRq q half :=
    AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half)
  have hindex : half - 1 + 1 = half := by omega
  have hroot : root ^ half = -1 := by
    exact LatticeCrypto.mk_X_pow_n (R := ZMod q) (n := half)
  change (-root ^ (half - 1)) * (root * RLWE.quotientOf hhalf value) =
    RLWE.quotientOf hhalf value
  calc
    (-root ^ (half - 1)) * (root * RLWE.quotientOf hhalf value) =
        -(root ^ (half - 1 + 1)) * RLWE.quotientOf hhalf value := by
          rw [pow_succ]
          ring
    _ = -(root ^ half) * RLWE.quotientOf hhalf value := by rw [hindex]
    _ = RLWE.quotientOf hhalf value := by rw [hroot]; ring

@[simp]
theorem rootTwist_rootUntwist (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (value : RLWE.Rq q half) :
    rootTwist q half hhalf (rootUntwist q half hhalf value) = value := by
  apply RLWE.quotientOf_injective (q := q) hhalf
  unfold rootUntwist rootTwist
  unfold proofMul
  rw [RLWE.quotientOf_commRing_mul, RLWE.quotientOf_commRing_mul,
    quotientOf_smallRootInverseRq, quotientOf_smallRootRq]
  let root : RLWE.QuotientRq q half :=
    AdjoinRoot.root (LatticeCrypto.negacyclicModulus (ZMod q) half)
  have hindex : half - 1 + 1 = half := by omega
  have hroot : root ^ half = -1 := by
    exact LatticeCrypto.mk_X_pow_n (R := ZMod q) (n := half)
  change root * ((-root ^ (half - 1)) * RLWE.quotientOf hhalf value) =
    RLWE.quotientOf hhalf value
  calc
    root * ((-root ^ (half - 1)) * RLWE.quotientOf hhalf value) =
        -(root ^ (half - 1 + 1)) * RLWE.quotientOf hhalf value := by
          rw [pow_succ]
          ring
    _ = -(root ^ half) * RLWE.quotientOf hhalf value := by rw [hindex]
    _ = RLWE.quotientOf hhalf value := by rw [hroot]; ring

/-- Multiplication by `Y` as an explicit permutation of the small executable ring. -/
noncomputable def rootTwistEquiv (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) : RLWE.Rq q half ≃ RLWE.Rq q half where
  toFun := rootTwist q half hhalf
  invFun := rootUntwist q half hhalf
  left_inv := rootUntwist_rootTwist q half hhalf
  right_inv := rootTwist_rootUntwist q half hhalf

/-- After undoing the public twist in the odd mask component, multiplication produces two
untwisted ordinary small-ring products. -/
theorem joinRq_commRing_mul_odd_untwist (q half : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (maskEven desiredEven secret : RLWE.Rq q half) :
    proofMul q (2 * half)
        (joinRq q half maskEven (rootUntwist q half hhalf desiredEven))
        (joinRq q half 0 secret) =
      joinRq q half (proofMul q half desiredEven secret)
        (proofMul q half maskEven secret) := by
  have identity := joinRq_commRing_mul_odd q half hhalf maskEven
    (rootUntwist q half hhalf desiredEven) secret
  change proofMul q (2 * half)
      (joinRq q half maskEven (rootUntwist q half hhalf desiredEven))
      (joinRq q half 0 secret) =
    joinRq q half
      (proofMul q half
        (rootTwist q half hhalf (rootUntwist q half hhalf desiredEven)) secret)
      (proofMul q half maskEven secret) at identity
  rw [rootTwist_rootUntwist] at identity
  exact identity

/-- Place a smaller coefficient vector in the even coordinates. -/
def evenCoefficients {R : Type} [Zero R] {half : ℕ} (value : Fin half → R) :
    Fin (2 * half) → R :=
  (coefficientParityEquiv R half).symm (value, 0)

/-- Place a smaller coefficient vector in the odd coordinates. -/
def oddCoefficients {R : Type} [Zero R] {half : ℕ} (value : Fin half → R) :
    Fin (2 * half) → R :=
  (coefficientParityEquiv R half).symm (0, value)

@[simp]
theorem split_evenCoefficients {R : Type} [Zero R] {half : ℕ}
    (value : Fin half → R) :
    coefficientParityEquiv R half (evenCoefficients value) = (value, 0) := by
  simp [evenCoefficients]

@[simp]
theorem split_oddCoefficients {R : Type} [Zero R] {half : ℕ}
    (value : Fin half → R) :
    coefficientParityEquiv R half (oddCoefficients value) = (0, value) := by
  simp [oddCoefficients]

end

end FormalProof4FHE.RLWE.EvenOddDecomposition
