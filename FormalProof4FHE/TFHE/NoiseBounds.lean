/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BlindRotation
import FormalProof4FHE.TFHE.SampleExtraction
import LatticeCrypto.Ring.Norms

/-!
# Quantitative TFHE Noise Foundations

This file starts the quantitative correctness layer for the finite-modulus TFHE model.  It proves
sound centered-coefficient bounds for modular addition and multiplication, lifts them to the
executable negacyclic ring, checks the infinity norm of the concrete base digits, and gives a first
worst-case bound for the weighted TGSW external-product row error.

The multiplication bound in this initial layer is deliberately conservative: it counts all
`N²` coefficient pairs in the executable convolution.  `TFHE.SharpRotationNoise` supplies the
refinement: a generic linear convolution estimate and exact norm preservation for native signed
rotations.  No unproved analytic inequality is hidden behind either bound.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NoiseBounds

noncomputable section

/-- Canonical proof-facing positive-degree ring dictionary for quantitative TFHE theorems. -/
@[reducible] noncomputable def positiveRqCommRing {q degree : ℕ} :
    CommRing (RLWE.Rq q (degree + 1)) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) (degree + 1)

@[reducible] noncomputable def positiveRqRing {q degree : ℕ} :
    Ring (RLWE.Rq q (degree + 1)) :=
  positiveRqCommRing.toRing

attribute [local instance] positiveRqCommRing positiveRqRing

private theorem rqPositive_zero_eq_bundled {q degree : ℕ} :
    @Zero.zero (RLWE.Rq q (degree + 1)) positiveRqCommRing.toZero =
      (RLWE.negacyclicRing q (degree + 1)).zero := by
  rfl

/-! ## Centered scalar inequalities -/

/-- Centered modular addition is no larger than the sum of centered absolute representatives. -/
theorem centeredRepr_add_natAbs_le {q : ℕ} [NeZero q] (left right : ZMod q) :
    (LatticeCrypto.centeredRepr (left + right)).natAbs ≤
      (LatticeCrypto.centeredRepr left).natAbs +
        (LatticeCrypto.centeredRepr right).natAbs := by
  rw [LatticeCrypto.centeredRepr_eq_valMinAbs,
    LatticeCrypto.centeredRepr_eq_valMinAbs,
    LatticeCrypto.centeredRepr_eq_valMinAbs]
  exact (ZMod.natAbs_valMinAbs_add_le left right).trans
    (Int.natAbs_add_le left.valMinAbs right.valMinAbs)

/-- Centered modular subtraction is no larger than the sum of the two centered absolute
representatives. -/
theorem centeredRepr_sub_natAbs_le {q : ℕ} [NeZero q] (left right : ZMod q) :
    (LatticeCrypto.centeredRepr (left - right)).natAbs ≤
      (LatticeCrypto.centeredRepr left).natAbs +
        (LatticeCrypto.centeredRepr right).natAbs := by
  rw [sub_eq_add_neg]
  exact (centeredRepr_add_natAbs_le left (-right)).trans_eq
    (congrArg (fun value ↦ (LatticeCrypto.centeredRepr left).natAbs + value)
      (LatticeCrypto.centeredRepr_natAbs_neg right))

/-- Centered modular multiplication is no larger than multiplying centered representatives. -/
theorem centeredRepr_mul_natAbs_le {q : ℕ} [NeZero q] (left right : ZMod q) :
    (LatticeCrypto.centeredRepr (left * right)).natAbs ≤
      (LatticeCrypto.centeredRepr left).natAbs *
        (LatticeCrypto.centeredRepr right).natAbs := by
  rw [LatticeCrypto.centeredRepr_eq_valMinAbs,
    LatticeCrypto.centeredRepr_eq_valMinAbs,
    LatticeCrypto.centeredRepr_eq_valMinAbs]
  calc
    (left * right).valMinAbs.natAbs ≤
        (left.valMinAbs * right.valMinAbs).natAbs := by
      apply ZMod.natAbs_min_of_le_div_two q
      · simp
      · exact ZMod.natAbs_valMinAbs_le (left * right)
    _ = left.valMinAbs.natAbs * right.valMinAbs.natAbs := Int.natAbs_mul _ _

/-- The centered representative is minimal among all congruent integer representatives. -/
theorem centeredRepr_intCast_natAbs_le {q : ℕ} [NeZero q] (value : ℤ) :
    (LatticeCrypto.centeredRepr (value : ZMod q)).natAbs ≤ value.natAbs := by
  rw [LatticeCrypto.centeredRepr_eq_valMinAbs]
  apply ZMod.natAbs_min_of_le_div_two q
  · simp
  · exact ZMod.natAbs_valMinAbs_le (value : ZMod q)

/-- Natural casts are a convenient specialization of centered minimality. -/
theorem centeredRepr_natCast_natAbs_le {q : ℕ} [NeZero q] (value : ℕ) :
    (LatticeCrypto.centeredRepr (value : ZMod q)).natAbs ≤ value := by
  simpa using centeredRepr_intCast_natAbs_le (q := q) (value : ℤ)

/-- Centered absolute value of a finite modular sum is bounded by the sum of centered absolute
values. -/
theorem centeredRepr_finset_sum_natAbs_le {q : ℕ} [NeZero q]
    {Index : Type} [DecidableEq Index]
    (values : Index → ZMod q) (indices : Finset Index) :
    (LatticeCrypto.centeredRepr (∑ index ∈ indices, values index)).natAbs ≤
      ∑ index ∈ indices, (LatticeCrypto.centeredRepr (values index)).natAbs := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [LatticeCrypto.centeredRepr_eq_valMinAbs]
  | @insert index indices hnotmem ih =>
      simp only [Finset.sum_insert hnotmem]
      exact (centeredRepr_add_natAbs_le (values index)
        (∑ item ∈ indices, values item)).trans (Nat.add_le_add_left ih _)

/-! ## Executable negacyclic-ring infinity norm -/

/-- The centered infinity norm of the coefficientwise zero polynomial is zero. -/
@[simp]
theorem cInfNorm_zero {q degree : ℕ} [NeZero q] :
    LatticeCrypto.cInfNorm
      (0 : LatticeCrypto.Poly (ZMod q) degree) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  rw [LatticeCrypto.Poly.get_zero]
  simp [LatticeCrypto.centeredRepr_eq_valMinAbs]

/-- Infinity norm is subadditive for the vector-backed polynomial carrier. -/
theorem cInfNorm_add_le {q degree : ℕ} [NeZero q]
    (left right : RLWE.Rq q degree) :
    LatticeCrypto.cInfNorm (left + right) ≤
      LatticeCrypto.cInfNorm left + LatticeCrypto.cInfNorm right := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  have hadd : (left + right).get coefficient =
      left.get coefficient + right.get coefficient :=
    Vector.getElem_add left right coefficient.val coefficient.isLt
  rw [hadd]
  exact (centeredRepr_add_natAbs_le (left.get coefficient) (right.get coefficient)).trans
    (Nat.add_le_add
      (LatticeCrypto.coeff_le_cInfNorm left coefficient)
      (LatticeCrypto.coeff_le_cInfNorm right coefficient))

/-- Infinity norm is subadditive under polynomial subtraction. -/
theorem cInfNorm_sub_le {q degree : ℕ} [NeZero q]
    (left right : RLWE.Rq q degree) :
    LatticeCrypto.cInfNorm (left - right) ≤
      LatticeCrypto.cInfNorm left + LatticeCrypto.cInfNorm right := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  have hsub : (left - right).get coefficient =
      left.get coefficient - right.get coefficient :=
    Vector.getElem_sub left right coefficient.val coefficient.isLt
  rw [hsub]
  exact (centeredRepr_sub_natAbs_le (left.get coefficient) (right.get coefficient)).trans
    (Nat.add_le_add
      (LatticeCrypto.coeff_le_cInfNorm left coefficient)
      (LatticeCrypto.coeff_le_cInfNorm right coefficient))

/-- Infinity norm of a finite polynomial sum is bounded by the sum of the individual norms. -/
theorem cInfNorm_finset_sum_le {q degree : ℕ} [NeZero q]
    {Index : Type} [DecidableEq Index]
    (values : Index → RLWE.Rq q (degree + 1)) (indices : Finset Index) :
    LatticeCrypto.cInfNorm
        (@Finset.sum Index (RLWE.Rq q (degree + 1))
          positiveRqCommRing.toAddCommMonoid indices values) ≤
      ∑ index ∈ indices, LatticeCrypto.cInfNorm (values index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      have hsum :
          @Finset.sum Index (RLWE.Rq q (degree + 1))
              positiveRqCommRing.toAddCommMonoid ∅ values =
            (0 : LatticeCrypto.Poly (ZMod q) (degree + 1)) := by
        rw [Finset.sum_empty]
        calc
          @Zero.zero (RLWE.Rq q (degree + 1)) positiveRqCommRing.toZero =
              (RLWE.negacyclicRing q (degree + 1)).zero := rqPositive_zero_eq_bundled
          _ = (0 : LatticeCrypto.Poly (ZMod q) (degree + 1)) :=
            LatticeCrypto.vectorRing_zero
      rw [hsum, Finset.sum_empty]
      apply LatticeCrypto.cInfNorm_le_of_coeff_le
      intro coefficient
      rw [LatticeCrypto.Poly.get_zero]
      simp [LatticeCrypto.centeredRepr_eq_valMinAbs]
  | @insert index indices hnotmem ih =>
      simp only [Finset.sum_insert hnotmem]
      exact (cInfNorm_add_le (values index)
        (∑ item ∈ indices, values item)).trans (Nat.add_le_add_left ih _)

/-- A coefficient of executable multiplication is the checked negacyclic convolution formula. -/
theorem mul_coefficient {q degree : ℕ} [NeZero q]
    (left right : RLWE.Rq q (degree + 1)) (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi (left * right) coefficient =
      LatticeCrypto.negacyclicConvCoeff
        (LatticeCrypto.Poly.toPi left) (LatticeCrypto.Poly.toPi right) coefficient := by
  change (LatticeCrypto.vectorBackend (ZMod q) (degree + 1)).coeff
      ((LatticeCrypto.vectorNegacyclicRing (ZMod q) (degree + 1)).mul left right)
        coefficient =
      LatticeCrypto.negacyclicConvCoeff
        ((LatticeCrypto.vectorBackend (ZMod q) (degree + 1)).coeff left)
        ((LatticeCrypto.vectorBackend (ZMod q) (degree + 1)).coeff right) coefficient
  simp only [LatticeCrypto.vectorNegacyclicRing_mul,
    LatticeCrypto.negacyclicMulPure_coeff]

/-- Conservative checked convolution bound for centered infinity norm. -/
theorem cInfNorm_mul_le {q degree : ℕ} [NeZero q]
    (left right : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm (left * right) ≤
      ((degree + 1) * (degree + 1)) *
        (LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right) := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  rw [show (left * right).get coefficient =
      LatticeCrypto.negacyclicConvCoeff
        (LatticeCrypto.Poly.toPi left) (LatticeCrypto.Poly.toPi right) coefficient by
    exact mul_coefficient left right coefficient]
  let term : Fin (degree + 1) × Fin (degree + 1) → ZMod q := fun index ↦
    if (index.1.val + index.2.val) % (degree + 1) = coefficient.val then
      if index.1.val + index.2.val < degree + 1 then
        left.get index.1 * right.get index.2
      else -(left.get index.1 * right.get index.2)
    else 0
  have hterm (index : Fin (degree + 1) × Fin (degree + 1)) :
      (LatticeCrypto.centeredRepr (term index)).natAbs ≤
        LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right := by
    dsimp only [term]
    split_ifs
    · exact (centeredRepr_mul_natAbs_le (left.get index.1) (right.get index.2)).trans
        (Nat.mul_le_mul
          (LatticeCrypto.coeff_le_cInfNorm left index.1)
          (LatticeCrypto.coeff_le_cInfNorm right index.2))
    · rw [LatticeCrypto.centeredRepr_natAbs_neg]
      exact (centeredRepr_mul_natAbs_le (left.get index.1) (right.get index.2)).trans
        (Nat.mul_le_mul
          (LatticeCrypto.coeff_le_cInfNorm left index.1)
          (LatticeCrypto.coeff_le_cInfNorm right index.2))
    · simp [LatticeCrypto.centeredRepr_eq_valMinAbs]
  change (LatticeCrypto.centeredRepr (∑ index, term index)).natAbs ≤ _
  calc
    (LatticeCrypto.centeredRepr (∑ index, term index)).natAbs ≤
        ∑ index, (LatticeCrypto.centeredRepr (term index)).natAbs := by
      simpa using centeredRepr_finset_sum_natAbs_le term Finset.univ
    _ ≤ ∑ _index : Fin (degree + 1) × Fin (degree + 1),
        LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right :=
      Finset.sum_le_sum fun index _ ↦ hterm index
    _ = ((degree + 1) * (degree + 1)) *
        (LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right) := by
      simp [Fintype.card_prod]

/-! ## Concrete digit and external-product bounds -/

/-- Every coefficientwise executable base digit has centered infinity norm at most `B - 1`. -/
theorem cInfNorm_ringDigit_le {q degree : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (value : RLWE.Rq q degree)
    (level : Fin params.levels) :
    LatticeCrypto.cInfNorm (Gadget.Base.ringDigit params value level) ≤
      params.base - 1 := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  have hcoefficient := Gadget.Base.ringDigit_coefficient params value level coefficient
  change (Gadget.Base.ringDigit params value level).get coefficient = _ at hcoefficient
  rw [hcoefficient]
  unfold Gadget.Base.digit
  calc
    (LatticeCrypto.centeredRepr
        (Gadget.Base.natDigit params (LatticeCrypto.Poly.toPi value coefficient) level :
          ZMod q)).natAbs ≤
        (Gadget.Base.natDigit params
          (LatticeCrypto.Poly.toPi value coefficient) level : ℤ).natAbs :=
      centeredRepr_natCast_natAbs_le (q := q) _
    _ = Gadget.Base.natDigit params
          (LatticeCrypto.Poly.toPi value coefficient) level := by simp
    _ ≤ params.base - 1 := by
      have := Gadget.Base.natDigit_lt_base params
        (LatticeCrypto.Poly.toPi value coefficient) level
      omega

/-- First sound worst-case bound for the weighted row-error term of one TGSW external product. -/
theorem cInfNorm_externalProductError_le
    {q degree dimension levels : ℕ} [NeZero q]
    (secret : Fin dimension → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (message : RLWE.Rq q (degree + 1))
    (digits : Fin (dimension + 1) → Fin levels → RLWE.Rq q (degree + 1))
    (ciphertext : TGSW.Ciphertext (RLWE.Rq q (degree + 1)) dimension levels)
    (digitBound rowErrorBound : ℕ)
    (hdigits : ∀ block level, LatticeCrypto.cInfNorm (digits block level) ≤ digitBound)
    (hrows : ∀ index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret gadget message ciphertext index) ≤
        rowErrorBound) :
    LatticeCrypto.cInfNorm
        (TGSW.externalProductError (R := RLWE.Rq q (degree + 1))
          secret gadget message digits ciphertext) ≤
      ((dimension + 1) * levels) *
        (((degree + 1) * (degree + 1)) * (digitBound * rowErrorBound)) := by
  unfold TGSW.externalProductError
  calc
    LatticeCrypto.cInfNorm
        (@Finset.sum (Fin (dimension + 1) × Fin levels)
          (RLWE.Rq q (degree + 1)) positiveRqRing.toAddCommMonoid Finset.univ
          (fun index ↦ digits index.1 index.2 *
            TGSW.rowError (R := RLWE.Rq q (degree + 1))
              secret gadget message ciphertext index)) ≤
        ∑ index : Fin (dimension + 1) × Fin levels,
          LatticeCrypto.cInfNorm
            (digits index.1 index.2 *
              TGSW.rowError (R := RLWE.Rq q (degree + 1))
                secret gadget message ciphertext index) := by
      simpa using cInfNorm_finset_sum_le
        (fun index : Fin (dimension + 1) × Fin levels ↦
          digits index.1 index.2 *
            TGSW.rowError (R := RLWE.Rq q (degree + 1))
              secret gadget message ciphertext index)
        Finset.univ
    _ ≤ ∑ _index : Fin (dimension + 1) × Fin levels,
        ((degree + 1) * (degree + 1)) * (digitBound * rowErrorBound) := by
      apply Finset.sum_le_sum
      intro index _
      exact (cInfNorm_mul_le (digits index.1 index.2)
        (TGSW.rowError (R := RLWE.Rq q (degree + 1))
          secret gadget message ciphertext index)).trans
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul (hdigits index.1 index.2) (hrows index)))
    _ = ((dimension + 1) * levels) *
        (((degree + 1) * (degree + 1)) * (digitBound * rowErrorBound)) := by
      simp [Fintype.card_prod]

/-- External-product error bound specialized to the checked executable base digits. -/
theorem cInfNorm_externalProductError_ringDigits_le
    {q degree dimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin dimension → RLWE.Rq q (degree + 1))
    (message : RLWE.Rq q (degree + 1))
    (input : TLWE.Ciphertext (RLWE.Rq q (degree + 1)) dimension)
    (ciphertext : TGSW.Ciphertext
      (RLWE.Rq q (degree + 1)) dimension params.levels)
    (rowErrorBound : ℕ)
    (hrows : ∀ index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params) message ciphertext index) ≤ rowErrorBound) :
    LatticeCrypto.cInfNorm
        (TGSW.externalProductError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) message
            (Gadget.Base.ringExtendedDigits params input) ciphertext) ≤
      ((dimension + 1) * params.levels) *
        (((degree + 1) * (degree + 1)) * ((params.base - 1) * rowErrorBound)) := by
  apply cInfNorm_externalProductError_le secret (Gadget.Base.ringGadget params) message
    (Gadget.Base.ringExtendedDigits params input) ciphertext (params.base - 1)
      rowErrorBound
  · intro block level
    exact cInfNorm_ringDigit_le params (Gadget.extendedCiphertext input block) level
  · exact hrows

end

end FormalProof4FHE.TFHE.NoiseBounds
