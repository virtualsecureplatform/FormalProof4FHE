/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CoefficientAffineCircularRLWE
import FormalProof4FHE.TFHE.RingSquareRGSWSecurity
import FormalProof4FHE.TFHE.RotationLookup

open scoped BigOperators

/-!
# The Highest Two-Adic Row of `RGSW_S(-S)`

Let the coefficient modulus be `q = 2^(k+1)` and put `h = 2^k`.  Since `2*h = 0`
modulo `q`, multiplication by `h` kills every off-diagonal term in the square of a
Boolean-coefficient polynomial:

`h * (∑_i s_i X^i)^2 = ∑_i s_i * h * X^(2i)`.

This file proves that identity in the executable negacyclic ring and connects it to the
highest-weight upper row of the stripped rank-one `RGSW_S(-S)` normal form.  The row keeps the
fresh narrow error unchanged.  Its plaintext is a fixed coefficient-linear operator applied to
the binary coefficient vector, so the complete upper-square/lower-zero pair is an exact instance
of coefficient-affine circular RLWE.

The linearization is not an ordinary rank-one RLWE reduction.  In ring degree at least two the
map `S ↦ h*S^2`, even restricted to Boolean polynomials, is not multiplication by any fixed
public ring element.  Thus it cannot be absorbed by the standard public challenge translation.
The named coefficient-affine problem below is the precise remaining hardness endpoint for this
top row; lower two-adic gadget weights and the full native RGSW matrix remain separate research
obligations.
-/

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightCoefficientAffine

theorem weighted_sq_add {R : Type} [CommRing R]
    (weight left right : R) (hweight : 2 * weight = 0) :
    weight * (left + right) ^ 2 =
      weight * left ^ 2 + weight * right ^ 2 := by
  calc
    weight * (left + right) ^ 2 =
        weight * left ^ 2 + weight * right ^ 2 +
          (2 * weight) * (left * right) := by ring
    _ = weight * left ^ 2 + weight * right ^ 2 := by rw [hweight, zero_mul, add_zero]

theorem weighted_sq_sum {R Index : Type} [CommRing R] [Fintype Index]
    [DecidableEq Index]
    (weight : R) (values : Index → R) (hweight : 2 * weight = 0) :
    weight * (∑ index, values index) ^ 2 =
      ∑ index, weight * (values index) ^ 2 := by
  have hfinite : ∀ indices : Finset Index,
      weight * (∑ index ∈ indices, values index) ^ 2 =
        ∑ index ∈ indices, weight * (values index) ^ 2 := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert element rest hnotmem induction =>
        simp only [Finset.sum_insert hnotmem]
        rw [weighted_sq_add weight _ _ hweight, induction]
  simpa using hfinite Finset.univ

theorem bool_term_sq {R : Type} [CommRing R]
    (bit : Bool) (value : R) :
    (if bit then value else 0) ^ 2 = if bit then value ^ 2 else 0 := by
  cases bit <;> simp

theorem weighted_bool_sum_sq {R Index : Type} [CommRing R] [Fintype Index]
    [DecidableEq Index]
    (weight : R) (bits : Index → Bool) (basis : Index → R)
    (hweight : 2 * weight = 0) :
    weight * (∑ index, if bits index then basis index else 0) ^ 2 =
      ∑ index, if bits index then weight * (basis index) ^ 2 else 0 := by
  classical
  rw [weighted_sq_sum weight (fun index ↦ if bits index then basis index else 0) hweight]
  apply Finset.sum_congr rfl
  intro index _
  rw [bool_term_sq]
  split <;> simp_all

def binaryBasis (q degree : ℕ) (coordinate : Fin degree) :
    FormalProof4FHE.RLWE.Rq q degree :=
  FormalProof4FHE.TFHE.embedBinaryPolynomial q degree
    (FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit coordinate true)

theorem embedBinaryPolynomial_eq_sum_basis
    (q degree : ℕ) [NeZero q]
    (secret : Fin (degree + 1) → Bool) :
    FormalProof4FHE.TFHE.embedBinaryPolynomial q (degree + 1) secret =
      ∑ coordinate, if secret coordinate then
        binaryBasis q (degree + 1) coordinate else 0 := by
  classical
  apply LatticeCrypto.Poly.ext_get_eq
  intro output
  change FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom (degree + 1) output
      (FormalProof4FHE.TFHE.embedBinaryPolynomial q (degree + 1) secret) =
    FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom (degree + 1) output
      (∑ coordinate, if secret coordinate then binaryBasis q (degree + 1) coordinate else 0)
  rw [map_sum]
  have hleft :
      FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom (degree + 1) output
          (FormalProof4FHE.TFHE.embedBinaryPolynomial q (degree + 1) secret) =
        if secret output then (1 : ZMod q) else 0 := by
    simp [FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom_apply,
      FormalProof4FHE.TFHE.embedBinaryPolynomial,
      FormalProof4FHE.TFHE.embedBit]
  rw [hleft]
  have hterm : ∀ coordinate : Fin (degree + 1),
      FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom (degree + 1) output
          (if secret coordinate then binaryBasis q (degree + 1) coordinate else 0) =
        if secret coordinate then
          (if output = coordinate then (1 : ZMod q) else 0) else 0 := by
    intro coordinate
    by_cases hsecret : secret coordinate
    · simp [hsecret, FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom_apply,
        binaryBasis, FormalProof4FHE.TFHE.embedBinaryPolynomial,
        FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit,
        FormalProof4FHE.TFHE.embedBit]
    · simp [hsecret]
  simp_rw [hterm]
  rw [Finset.sum_eq_single output]
  · simp
  · intro coordinate _ hcoordinate
    simp [Ne.symm hcoordinate]
  · simp

theorem modulus_nsmul_one_eq_zero (exponent degree : ℕ) :
    (2 ^ (exponent + 1)) •
      (1 : FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) = 0 := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom (degree + 1) coefficient
      ((2 ^ (exponent + 1)) •
        (1 : FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) =
    FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom (degree + 1) coefficient 0
  rw [map_nsmul]
  simp only [FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom_apply]
  rw [FormalProof4FHE.TFHE.BlindRotation.rq_one_coefficient,
    FormalProof4FHE.TFHE.BlindRotation.rq_zero_coefficient]
  split
  · rw [nsmul_eq_mul]
    simp only [mul_one]
    exact ZMod.natCast_self _
  · simp

noncomputable def topWeight (exponent degree : ℕ) :
    FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
  (2 ^ exponent) • 1

theorem topWeight_annihilated (exponent degree : ℕ) :
    (2 : FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) *
        topWeight exponent degree = 0 := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  calc
    (2 : FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) *
        topWeight exponent degree =
      2 • topWeight exponent degree := by
        exact (nsmul_eq_mul 2 (topWeight exponent degree)).symm
    _ = (2 * 2 ^ exponent) •
        (1 : FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) := by
      exact (mul_nsmul'
        (1 : FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))
        2 (2 ^ exponent)).symm
    _ = (2 ^ (exponent + 1)) •
        (1 : FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)) := by
      congr 1
      rw [pow_succ]
      exact Nat.mul_comm 2 (2 ^ exponent)
    _ = 0 := modulus_nsmul_one_eq_zero exponent degree

noncomputable def topSquareLinearized (exponent degree : ℕ)
    (secret : Fin (degree + 1) → Bool) :
    FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
  ∑ coordinate, if secret coordinate then
    topWeight exponent degree *
      (binaryBasis (2 ^ (exponent + 1)) (degree + 1) coordinate) ^ 2
    else 0

theorem topWeight_mul_square_eq_linearized (exponent degree : ℕ)
    (secret : Fin (degree + 1) → Bool) :
    topWeight exponent degree *
        (FormalProof4FHE.TFHE.embedBinaryPolynomial
          (2 ^ (exponent + 1)) (degree + 1) secret) ^ 2 =
      topSquareLinearized exponent degree secret := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [embedBinaryPolynomial_eq_sum_basis]
  exact weighted_bool_sum_sq (topWeight exponent degree) secret
    (binaryBasis (2 ^ (exponent + 1)) (degree + 1))
    (topWeight_annihilated exponent degree)

theorem topSquareLinearized_singleBit (exponent degree : ℕ)
    (coordinate : Fin (degree + 1)) :
    topSquareLinearized exponent degree
        (FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit coordinate true) =
      topWeight exponent degree *
        binaryBasis (2 ^ (exponent + 1)) (degree + 1) coordinate ^ 2 := by
  classical
  unfold topSquareLinearized
  rw [Finset.sum_eq_single coordinate]
  · simp [FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit]
  · intro other _ hother
    simp [FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit, hother]
  · simp

def oneRotationExponent (extra : ℕ) : Fin (2 * ((extra + 1) + 1)) :=
  ⟨1, by omega⟩

def twoRotationExponent (extra : ℕ) : Fin (2 * ((extra + 1) + 1)) :=
  ⟨2, by omega⟩

theorem binaryBasis_second_eq_rotationMonomial
    (q extra : ℕ) [NeZero q] :
    binaryBasis q (extra + 2)
        (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra) =
      FormalProof4FHE.TFHE.BlindRotation.rotationMonomial q (extra + 1)
        (oneRotationExponent extra) := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change LatticeCrypto.Poly.toPi
      (binaryBasis q (extra + 2)
        (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra))
        coefficient =
    LatticeCrypto.Poly.toPi
      (FormalProof4FHE.TFHE.BlindRotation.rotationMonomial q (extra + 1)
        (oneRotationExponent extra)) coefficient
  unfold binaryBasis
  simp only [FormalProof4FHE.TFHE.embedBinaryPolynomial,
    LatticeCrypto.Poly.toPi_ofPi, FormalProof4FHE.TFHE.embedBit]
  rw [FormalProof4FHE.TFHE.BlindRotation.rotationMonomial_coefficient]
  simp only [FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit,
    oneRotationExponent]
  have hlt : 1 < extra + 1 + 1 := by omega
  by_cases hcoefficient : coefficient =
      FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra
  · subst coefficient
    simp [hlt, FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate]
  · have hval : coefficient.val ≠ 1 := by
      intro heq
      apply hcoefficient
      apply Fin.ext
      simpa [FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate]
        using heq
    simp [hlt, hcoefficient, hval]

theorem binaryBasis_first_eq_one (q extra : ℕ) [NeZero q] :
    binaryBasis q (extra + 2)
        (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.firstCoordinate extra) = 1 := by
  exact
    FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.embedBinaryPolynomial_single_first_eq_one
      q extra

theorem oneRotationExponent_add_self (extra : ℕ) :
    oneRotationExponent extra + oneRotationExponent extra =
      twoRotationExponent extra := by
  apply Fin.ext
  change (1 + 1) % (2 * ((extra + 1) + 1)) = 2
  rw [Nat.mod_eq_of_lt (by omega)]

theorem topWeight_mul_secondBasis_sq_ne_secondBasis_mul_topWeight
    (exponent extra : ℕ) :
    topWeight exponent (extra + 1) *
          binaryBasis (2 ^ (exponent + 1)) (extra + 2)
            (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra) ^ 2 ≠
      binaryBasis (2 ^ (exponent + 1)) (extra + 2)
          (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra) *
        topWeight exponent (extra + 1) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  intro heq
  rw [binaryBasis_second_eq_rotationMonomial, pow_two,
    FormalProof4FHE.TFHE.RotationLookup.rotationMonomial_mul,
    oneRotationExponent_add_self] at heq
  have hnormalized :
      (2 ^ exponent) •
          FormalProof4FHE.TFHE.BlindRotation.rotationMonomial
            (2 ^ (exponent + 1)) (extra + 1) (twoRotationExponent extra) =
        (2 ^ exponent) •
          FormalProof4FHE.TFHE.BlindRotation.rotationMonomial
            (2 ^ (exponent + 1)) (extra + 1) (oneRotationExponent extra) := by
    calc
      _ = topWeight exponent (extra + 1) *
          FormalProof4FHE.TFHE.BlindRotation.rotationMonomial
            (2 ^ (exponent + 1)) (extra + 1) (twoRotationExponent extra) := by
        simp only [topWeight, nsmul_eq_mul]
        ring
      _ = FormalProof4FHE.TFHE.BlindRotation.rotationMonomial
            (2 ^ (exponent + 1)) (extra + 1) (oneRotationExponent extra) *
          topWeight exponent (extra + 1) := heq
      _ = _ := by
        simp only [topWeight, nsmul_eq_mul]
        ring
  have hcoefficient := congrArg
    (FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom (extra + 2)
      (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra))
    hnormalized
  simp only [map_nsmul,
    FormalProof4FHE.TFHE.Gadget.Base.coefficientAddHom_apply] at hcoefficient
  rw [FormalProof4FHE.TFHE.BlindRotation.rotationMonomial_coefficient,
    FormalProof4FHE.TFHE.BlindRotation.rotationMonomial_coefficient] at hcoefficient
  have honeMod : 1 % (2 * ((extra + 1) + 1)) = 1 :=
    Nat.mod_eq_of_lt (by omega)
  simp [oneRotationExponent, twoRotationExponent,
    honeMod,
    FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate] at hcoefficient
  have hpositive : 0 < 2 ^ exponent := pow_pos (by omega) _
  have hlt : 2 ^ exponent < 2 ^ (exponent + 1) := by
    rw [pow_succ]
    omega
  have hnonzero :
      ((2 ^ exponent : ℕ) : ZMod (2 ^ (exponent + 1))) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hpositive hlt)
      ((ZMod.natCast_eq_zero_iff (2 ^ exponent) (2 ^ (exponent + 1))).mp hzero)
  have hcast : ((2 ^ exponent : ℕ) : ZMod (2 ^ (exponent + 1))) = 0 := by
    simpa [nsmul_eq_mul] using hcoefficient.symm
  exact hnonzero hcast

theorem topSquareLinearized_not_ringMultiplicationOnBinary
    (exponent extra : ℕ) :
    ¬ FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.RingMultiplicationOnBinary
      (2 ^ (exponent + 1)) (extra + 2)
      (topSquareLinearized exponent (extra + 1)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rintro ⟨multiplier, hrepresentation⟩
  have hfirst := hrepresentation
    (FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit
      (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.firstCoordinate extra) true)
  rw [topSquareLinearized_singleBit,
    binaryBasis_first_eq_one, one_pow, mul_one,
    FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.embedBinaryPolynomial_single_first_eq_one,
    one_mul] at hfirst
  have hmultiplier : multiplier = topWeight exponent (extra + 1) := hfirst.symm
  have hsecond := hrepresentation
    (FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit
      (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra) true)
  rw [topSquareLinearized_singleBit, hmultiplier] at hsecond
  change topWeight exponent (extra + 1) *
      binaryBasis (2 ^ (exponent + 1)) (extra + 2)
        (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra) ^ 2 =
    binaryBasis (2 ^ (exponent + 1)) (extra + 2)
        (FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.secondCoordinate extra) *
      topWeight exponent (extra + 1) at hsecond
  exact (topWeight_mul_secondBasis_sq_ne_secondBasis_mul_topWeight
    exponent extra) hsecond

theorem square_mul_topWeight_eq_linearized (exponent degree : ℕ)
    (secret : Fin (degree + 1) → Bool) :
    let embedded := FormalProof4FHE.TFHE.embedBinaryPolynomial
      (2 ^ (exponent + 1)) (degree + 1) secret
    embedded * embedded * topWeight exponent degree =
      topSquareLinearized exponent degree secret := by
  dsimp only
  rw [← topWeight_mul_square_eq_linearized exponent degree secret]
  ring

noncomputable def topGadget (exponent degree : ℕ) :
    Fin 1 → FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
  fun _ ↦ topWeight exponent degree

theorem squareMessages_topGadget_upper_eq_linearized
    (exponent degree : ℕ) (secret : Fin (degree + 1) → Bool) :
    let embedded : Fin 1 →
        FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
      fun _ ↦ FormalProof4FHE.TFHE.embedBinaryPolynomial
        (2 ^ (exponent + 1)) (degree + 1) secret
    FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages
        embedded (topGadget exponent degree)
        (FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.upperRow (0 : Fin 1)) =
      topSquareLinearized exponent degree secret := by
  dsimp only
  rw [FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages_upper]
  exact square_mul_topWeight_eq_linearized exponent degree secret

theorem squareMessages_topGadget_lower_eq_zero
    (exponent degree : ℕ) (secret : Fin (degree + 1) → Bool) :
    let embedded : Fin 1 →
        FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
      fun _ ↦ FormalProof4FHE.TFHE.embedBinaryPolynomial
        (2 ^ (exponent + 1)) (degree + 1) secret
    FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages
        embedded (topGadget exponent degree)
        (FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.lowerRow (0 : Fin 1)) = 0 := by
  dsimp only
  exact FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages_lower _ _ _

noncomputable def topSquareBasisCoefficients (exponent degree : ℕ)
    (coordinate : Fin (degree + 1)) :
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.Coefficients
      (2 ^ (exponent + 1)) (degree + 1) :=
  FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
    (2 ^ (exponent + 1)) (degree + 1)
    (topWeight exponent degree *
      (binaryBasis (2 ^ (exponent + 1)) (degree + 1) coordinate) ^ 2)

noncomputable def topSquareOperator (exponent degree : ℕ) :
    FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.CoefficientOperator
      (2 ^ (exponent + 1)) (degree + 1) where
  toFun := fun value output ↦
    ∑ coordinate, value coordinate * topSquareBasisCoefficients exponent degree coordinate output
  map_add' := by
    intro left right
    funext output
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext output
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    rw [RingHom.id_apply]
    ac_rfl

@[simp]
theorem topSquareOperator_apply (exponent degree : ℕ)
    (value :
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.Coefficients
        (2 ^ (exponent + 1)) (degree + 1))
    (output : Fin (degree + 1)) :
    topSquareOperator exponent degree value output =
      ∑ coordinate,
        value coordinate * topSquareBasisCoefficients exponent degree coordinate output :=
  rfl

theorem coefficientEquiv_topSquareLinearized (exponent degree : ℕ)
    (secret : Fin (degree + 1) → Bool) :
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (degree + 1)
        (topSquareLinearized exponent degree secret) =
      topSquareOperator exponent degree
        (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients
          (2 ^ (exponent + 1)) secret) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  unfold topSquareLinearized
  rw [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_sum]
  funext output
  simp only [topSquareOperator_apply]
  rw [Finset.sum_apply]
  change (∑ coordinate,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
          (2 ^ (exponent + 1)) (degree + 1)
          (if secret coordinate then
            topWeight exponent degree *
              binaryBasis (2 ^ (exponent + 1)) (degree + 1) coordinate ^ 2
          else 0) output) =
    ∑ coordinate,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients
          (2 ^ (exponent + 1)) secret coordinate *
        topSquareBasisCoefficients exponent degree coordinate output
  apply Finset.sum_congr rfl
  intro coordinate _
  cases hsecret : secret coordinate
  · simp [hsecret,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
      FormalProof4FHE.TFHE.embedBit,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_zero]
  · simp [hsecret,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
      FormalProof4FHE.TFHE.embedBit, topSquareBasisCoefficients]

theorem coefficientEquiv_mul_add_topSquare (exponent degree : ℕ)
    (secret : Fin (degree + 1) → Bool)
    (challenge : FormalProof4FHE.RLWE.Rq
      (2 ^ (exponent + 1)) (degree + 1)) :
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (degree + 1)
        (FormalProof4FHE.TFHE.embedBinaryPolynomial
            (2 ^ (exponent + 1)) (degree + 1) secret * challenge +
          topSquareLinearized exponent degree secret) =
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.negacyclicProduct
          (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients
            (2 ^ (exponent + 1)) secret)
          (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
            (2 ^ (exponent + 1)) (degree + 1) challenge) +
        topSquareOperator exponent degree
          (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients
            (2 ^ (exponent + 1)) secret) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_mul,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
    coefficientEquiv_topSquareLinearized]

noncomputable def topSquareOperators (exponent degree : ℕ) :
    Fin 1 →
      FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.CoefficientOperator
        (2 ^ (exponent + 1)) (degree + 1) :=
  fun _ ↦ topSquareOperator exponent degree

theorem coefficientAffineNoiseless_topSquareOperators
    (exponent degree : ℕ) (secret : Fin (degree + 1) → Bool)
    (challenge :
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.Challenge
        (2 ^ (exponent + 1)) (degree + 1) 1 1) :
    FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.coefficientAffineNoiseless
        (topSquareOperators exponent degree) secret challenge 0 =
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (degree + 1)
        (FormalProof4FHE.TFHE.embedBinaryPolynomial
            (2 ^ (exponent + 1)) (degree + 1) secret *
          (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
            (2 ^ (exponent + 1)) (degree + 1)).symm (challenge 0 0) +
          topSquareLinearized exponent degree secret) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [coefficientEquiv_mul_add_topSquare]
  simp [FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.coefficientAffineNoiseless,
    topSquareOperators]

noncomputable def topRGSWLinearizedMessages (exponent degree : ℕ)
    (secret : Fin (degree + 1) → Bool) :
    Fin (FormalProof4FHE.TFHE.TGSW.rowCount 1 1) →
      FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
  fun row ↦
    if (FormalProof4FHE.TFHE.TGSW.rowIndex row).1 = 0 then
      topSquareLinearized exponent degree secret
    else 0

theorem squareMessages_topGadget_eq_linearized
    (exponent degree : ℕ) (secret : Fin (degree + 1) → Bool) :
    let embedded : Fin 1 →
        FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
      fun _ ↦ FormalProof4FHE.TFHE.embedBinaryPolynomial
        (2 ^ (exponent + 1)) (degree + 1) secret
    FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages
        embedded (topGadget exponent degree) =
      topRGSWLinearizedMessages exponent degree secret := by
  dsimp only
  funext row
  unfold FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages
    topRGSWLinearizedMessages topGadget
  dsimp only
  split
  · exact square_mul_topWeight_eq_linearized exponent degree secret
  · rfl

noncomputable def topRGSWOperators (exponent degree : ℕ) :
    Fin (FormalProof4FHE.TFHE.TGSW.rowCount 1 1) →
      FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.CoefficientOperator
        (2 ^ (exponent + 1)) (degree + 1) :=
  fun row ↦
    if (FormalProof4FHE.TFHE.TGSW.rowIndex row).1 = 0 then
      topSquareOperator exponent degree
    else 0

theorem coefficientEquiv_topRGSWLinearizedMessages
    (exponent degree : ℕ) (secret : Fin (degree + 1) → Bool)
    (row : Fin (FormalProof4FHE.TFHE.TGSW.rowCount 1 1)) :
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (degree + 1)
        (topRGSWLinearizedMessages exponent degree secret row) =
      topRGSWOperators exponent degree row
        (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients
          (2 ^ (exponent + 1)) secret) := by
  unfold topRGSWLinearizedMessages topRGSWOperators
  split
  · exact coefficientEquiv_topSquareLinearized exponent degree secret
  · simp [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_zero]

theorem coefficientEquiv_squareMessages_topGadget
    (exponent degree : ℕ) (secret : Fin (degree + 1) → Bool)
    (row : Fin (FormalProof4FHE.TFHE.TGSW.rowCount 1 1)) :
    let embedded : Fin 1 →
        FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
      fun _ ↦ FormalProof4FHE.TFHE.embedBinaryPolynomial
        (2 ^ (exponent + 1)) (degree + 1) secret
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (degree + 1)
        (FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages
          embedded (topGadget exponent degree) row) =
      topRGSWOperators exponent degree row
        (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients
          (2 ^ (exponent + 1)) secret) := by
  dsimp only
  rw [squareMessages_topGadget_eq_linearized exponent degree secret]
  exact coefficientEquiv_topRGSWLinearizedMessages exponent degree secret row

theorem coefficientAffineNoiseless_topRGSWOperators
    (exponent degree : ℕ) (secret : Fin (degree + 1) → Bool)
    (challenge :
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.Challenge
        (2 ^ (exponent + 1)) (degree + 1) 1
        (FormalProof4FHE.TFHE.TGSW.rowCount 1 1)) :
    let embedded : Fin 1 →
        FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
      fun _ ↦ FormalProof4FHE.TFHE.embedBinaryPolynomial
        (2 ^ (exponent + 1)) (degree + 1) secret
    FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.coefficientAffineNoiseless
        (topRGSWOperators exponent degree) secret challenge =
      fun row ↦
        FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
          (2 ^ (exponent + 1)) (degree + 1)
          (embedded 0 *
              (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
                (2 ^ (exponent + 1)) (degree + 1)).symm (challenge 0 row) +
            FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages
              embedded (topGadget exponent degree) row) := by
  dsimp only
  funext row
  unfold FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.coefficientAffineNoiseless
  rw [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_mul,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial]
  rw [(FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
    (2 ^ (exponent + 1)) (degree + 1)).apply_symm_apply]
  rw [coefficientEquiv_squareMessages_topGadget]

noncomputable def topRGSWCoefficientProblem
    (exponent degree : ℕ)
    (errorSampler : ProbComp
      (FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    LearningWithErrors.Problem
      (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.Challenge
        (2 ^ (exponent + 1)) (degree + 1) 1
        (FormalProof4FHE.TFHE.TGSW.rowCount 1 1))
      (FormalProof4FHE.TFHE.RingBinarySecret 1 (degree + 1))
      (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.Output
        (2 ^ (exponent + 1)) (degree + 1)
        (FormalProof4FHE.TFHE.TGSW.rowCount 1 1)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let ordinary :=
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.problem
      (2 ^ (exponent + 1)) (degree + 1) 1
      (FormalProof4FHE.TFHE.TGSW.rowCount 1 1) errorSampler
  exact
    { sampleChallenge := ordinary.sampleChallenge
      sampleSecret := ordinary.sampleSecret
      sampleError := ordinary.sampleError
      noiseless := fun ringSecret challenge ↦
        FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.coefficientAffineNoiseless
          (topRGSWOperators exponent degree) (ringSecret 0) challenge
      sampleUniform := ordinary.sampleUniform }

theorem topRGSWCoefficientProblem_same_samplers_as_ordinary
    (exponent degree : ℕ)
    (errorSampler : ProbComp
      (FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    let top := topRGSWCoefficientProblem exponent degree errorSampler
    let ordinary :=
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.problem
        (2 ^ (exponent + 1)) (degree + 1) 1
        (FormalProof4FHE.TFHE.TGSW.rowCount 1 1) errorSampler
    top.sampleChallenge = ordinary.sampleChallenge ∧
      top.sampleSecret = ordinary.sampleSecret ∧
      top.sampleError = ordinary.sampleError ∧
      top.sampleUniform = ordinary.sampleUniform := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  simp [topRGSWCoefficientProblem]

theorem topRGSWCoefficientProblem_noiseless
    (exponent degree : ℕ)
    (errorSampler : ProbComp
      (FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (ringSecret : FormalProof4FHE.TFHE.RingBinarySecret 1 (degree + 1))
    (challenge :
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.Challenge
        (2 ^ (exponent + 1)) (degree + 1) 1
        (FormalProof4FHE.TFHE.TGSW.rowCount 1 1)) :
    let embedded : Fin 1 →
        FormalProof4FHE.RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) :=
      fun _ ↦ FormalProof4FHE.TFHE.embedBinaryPolynomial
        (2 ^ (exponent + 1)) (degree + 1) (ringSecret 0)
    (topRGSWCoefficientProblem exponent degree errorSampler).noiseless
        ringSecret challenge =
      fun row ↦
        FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
          (2 ^ (exponent + 1)) (degree + 1)
          (embedded 0 *
              (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
                (2 ^ (exponent + 1)) (degree + 1)).symm (challenge 0 row) +
            FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Full.squareMessages
              embedded (topGadget exponent degree) row) := by
  dsimp only
  unfold topRGSWCoefficientProblem
  dsimp only
  exact coefficientAffineNoiseless_topRGSWOperators
    exponent degree (ringSecret 0) challenge

end FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightCoefficientAffine
