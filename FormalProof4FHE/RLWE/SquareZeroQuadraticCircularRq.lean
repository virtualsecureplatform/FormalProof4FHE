/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.SquareZeroQuadraticCircular
import FormalProof4FHE.TFHE.CoefficientStructuredLWE

/-!
# Executable negacyclic-ring square-zero extension

This file instantiates `SquareZeroQuadraticCircular.DigitExtension` coefficientwise between the
repository's executable rings `Rq p degree` and `Rq (p * p) degree`.

The executable polynomial carrier exposes primitive coefficient-vector operations as well as the
certified `CommRing` dictionary used by generic RLWE code.  We select the certified dictionary and
all of its operation projections locally.  The coefficient equivalence already certified for
structured LWE then keeps the representation bridge explicit.

The resulting maps are the expected formulas

* `lift f = [f]` coefficientwise,
* `high f = p [f]` coefficientwise, and
* `digits (f,g) = [f] + p[g]` coefficientwise.

The convolution proofs reduce every summand to the scalar `ZMod` square-zero laws.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.SquareZeroQuadraticCircular

noncomputable section

private abbrev coefficientEquiv :=
  FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv

/-! ## One coherent operation dictionary -/

local instance squareZeroRqCommRing (q degree : ℕ) : CommRing (Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance (priority := 1200) squareZeroRqAddCommGroup (q degree : ℕ) :
    AddCommGroup (Rq q degree) :=
  (squareZeroRqCommRing q degree).toAddCommGroup

local instance (priority := 1200) squareZeroRqAdd (q degree : ℕ) : Add (Rq q degree) :=
  (squareZeroRqAddCommGroup q degree).toAdd

local instance (priority := 1200) squareZeroRqSub (q degree : ℕ) : Sub (Rq q degree) :=
  (squareZeroRqCommRing q degree).toAddGroupWithOne.toAddGroup.toSub

local instance (priority := 1200) squareZeroRqNeg (q degree : ℕ) : Neg (Rq q degree) :=
  (squareZeroRqAddCommGroup q degree).toNeg

local instance (priority := 1200) squareZeroRqZero (q degree : ℕ) : Zero (Rq q degree) :=
  (squareZeroRqAddCommGroup q degree).toZero

local instance (priority := 1200) squareZeroRqMul (q degree : ℕ) : Mul (Rq q degree) :=
  (squareZeroRqCommRing q degree).toMul

local instance (priority := 1200) squareZeroRqOne (q degree : ℕ) : One (Rq q degree) :=
  (squareZeroRqCommRing q degree).toAddGroupWithOne.toOne

theorem coefficientEquiv_selected_zero (q degree : ℕ) :
    coefficientEquiv q degree (0 : Rq q degree) = 0 := by
  exact
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_semiring_zero
      q degree

theorem coefficientEquiv_selected_add (q degree : ℕ) (left right : Rq q degree) :
    coefficientEquiv q degree (left + right) =
      coefficientEquiv q degree left + coefficientEquiv q degree right := by
  exact
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_semiring_add
      q degree left right

theorem coefficientEquiv_selected_mul (q degree : ℕ) (left right : Rq q degree) :
    coefficientEquiv q degree (left * right) =
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.negacyclicProduct
        (coefficientEquiv q degree left) (coefficientEquiv q degree right) := by
  exact
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_semiring_mul
      q degree left right

/-! ## Coefficientwise digit maps -/

/-- Coefficientwise low-digit section. -/
def rqLift (p degree : ℕ) [NeZero p] (value : Rq p degree) : Rq (p * p) degree :=
  (coefficientEquiv (p * p) degree).symm fun coefficient ↦
    zmodLift p (coefficientEquiv p degree value coefficient)

@[simp]
theorem coefficientEquiv_rqLift (p degree : ℕ) [NeZero p] (value : Rq p degree) :
    coefficientEquiv (p * p) degree (rqLift p degree value) =
      fun coefficient ↦ zmodLift p (coefficientEquiv p degree value coefficient) :=
  (coefficientEquiv (p * p) degree).apply_symm_apply _

/-- Coefficientwise high-digit embedding `f ↦ p[f]`. -/
def rqHigh (p degree : ℕ) [NeZero p] : Rq p degree →+ Rq (p * p) degree where
  toFun value :=
    (coefficientEquiv (p * p) degree).symm fun coefficient ↦
      zmodHigh p (coefficientEquiv p degree value coefficient)
  map_zero' := by
    apply (coefficientEquiv (p * p) degree).injective
    rw [coefficientEquiv_selected_zero]
    simp only [Equiv.apply_symm_apply, coefficientEquiv_selected_zero, Pi.zero_apply, map_zero]
    funext coefficient
    rfl
  map_add' left right := by
    apply (coefficientEquiv (p * p) degree).injective
    rw [coefficientEquiv_selected_add]
    simp only [Equiv.apply_symm_apply, coefficientEquiv_selected_add, Pi.add_apply, map_add]
    funext coefficient
    rfl

@[simp]
theorem coefficientEquiv_rqHigh (p degree : ℕ) [NeZero p] (value : Rq p degree) :
    coefficientEquiv (p * p) degree (rqHigh p degree value) =
      fun coefficient ↦ zmodHigh p (coefficientEquiv p degree value coefficient) :=
  (coefficientEquiv (p * p) degree).apply_symm_apply _

/-- Pointwise two-digit decomposition of an executable negacyclic polynomial. -/
def rqDigitEquiv (p degree : ℕ) [NeZero p] :
    (Rq p degree × Rq p degree) ≃ Rq (p * p) degree :=
  ((coefficientEquiv p degree).prodCongr (coefficientEquiv p degree)).trans
    ((Equiv.arrowProdEquivProdArrow (Fin degree)
        (fun _ ↦ ZMod p) (fun _ ↦ ZMod p)).symm.trans
      ((Equiv.piCongrRight fun _ ↦ zmodDigitEquiv p).trans
        (coefficientEquiv (p * p) degree).symm))

@[simp]
theorem coefficientEquiv_rqDigitEquiv_apply (p degree : ℕ) [NeZero p]
    (low highDigit : Rq p degree) :
    coefficientEquiv (p * p) degree (rqDigitEquiv p degree (low, highDigit)) =
      fun coefficient ↦ zmodDigitEquiv p
        (coefficientEquiv p degree low coefficient,
          coefficientEquiv p degree highDigit coefficient) := by
  simp only [rqDigitEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.apply_symm_apply]
  rfl

@[simp]
theorem rqDigitEquiv_apply (p degree : ℕ) [NeZero p]
    (low highDigit : Rq p degree) :
    rqDigitEquiv p degree (low, highDigit) =
      rqLift p degree low + rqHigh p degree highDigit := by
  apply (coefficientEquiv (p * p) degree).injective
  rw [coefficientEquiv_selected_add]
  rw [coefficientEquiv_rqDigitEquiv_apply, coefficientEquiv_rqLift,
    coefficientEquiv_rqHigh]
  funext coefficient
  exact zmodDigitEquiv_apply p _ _

/-! ## Negacyclic convolution laws -/

/-- Multiplying a lifted polynomial by a high polynomial is base-ring convolution followed by
the high embedding. -/
theorem rqLift_mul_high (p degree : ℕ) [NeZero p]
    (left right : Rq p degree) :
    rqLift p degree left * rqHigh p degree right =
      rqHigh p degree (left * right) := by
  apply (coefficientEquiv (p * p) degree).injective
  rw [coefficientEquiv_selected_mul]
  rw [coefficientEquiv_rqLift, coefficientEquiv_rqHigh,
    coefficientEquiv_rqHigh,
    coefficientEquiv_selected_mul]
  funext coefficient
  change
    LatticeCrypto.negacyclicConvCoeff
        (fun index ↦ zmodLift p (coefficientEquiv p degree left index))
        (fun index ↦ zmodHigh p (coefficientEquiv p degree right index)) coefficient =
      zmodHigh p
        (LatticeCrypto.negacyclicConvCoeff
          (coefficientEquiv p degree left)
          (coefficientEquiv p degree right) coefficient)
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro indices _
  split_ifs
  · exact zmodLift_mul_zmodHigh p _ _
  · rw [map_neg, zmodLift_mul_zmodHigh]
  · simp

/-- The coefficientwise high image is a square-zero ideal. -/
theorem rqHigh_mul_high (p degree : ℕ) [NeZero p]
    (left right : Rq p degree) :
    rqHigh p degree left * rqHigh p degree right = 0 := by
  apply (coefficientEquiv (p * p) degree).injective
  rw [coefficientEquiv_selected_mul]
  rw [coefficientEquiv_rqHigh, coefficientEquiv_rqHigh,
    coefficientEquiv_selected_zero]
  funext coefficient
  change
    LatticeCrypto.negacyclicConvCoeff
        (fun index ↦ zmodHigh p (coefficientEquiv p degree left index))
        (fun index ↦ zmodHigh p (coefficientEquiv p degree right index)) coefficient = 0
  unfold LatticeCrypto.negacyclicConvCoeff
  apply Finset.sum_eq_zero
  intro indices _
  split_ifs
  · exact zmodHigh_mul_zmodHigh p _ _
  · rw [zmodHigh_mul_zmodHigh, neg_zero]
  · rfl

/-- Concrete coefficientwise square-zero extension `R_p → R_(p²)`. -/
def rqDigitExtension (p degree : ℕ) [NeZero p] :
    DigitExtension (Rq p degree) (Rq (p * p) degree) where
  lift := rqLift p degree
  high := rqHigh p degree
  digits := rqDigitEquiv p degree
  digits_apply := rqDigitEquiv_apply p degree
  lift_mul_high := rqLift_mul_high p degree
  high_mul_high := rqHigh_mul_high p degree

/-- End-to-end executable-ring specialization: distinguishing the `R_(p²)` quadratic-circular
batch from its matching zero-message batch costs at most the two indicated ordinary `R_p` RLWE
advantages.  The low secret digit may have any total sampler and the high secret/error laws are
arbitrary. -/
theorem rq_kdmAdvantage_le_two_base
    (p degree : ℕ) [NeZero p]
    {Row : Type} [Fintype Row] [DecidableEq Row]
    (weight : Row → Rq (p * p) degree)
    (lowSecretSampler highSecretSampler : ProbComp (Rq p degree))
    (highErrorSampler : ProbComp (Vector (Rq p degree) Row))
    (distinguisher : Distinguisher (Rq (p * p) degree) Row)
    (hLowSecret : Pr[⊥ | lowSecretSampler] = 0) :
    kdmAdvantage (rqDigitExtension p degree) weight lowSecretSampler highSecretSampler
        highErrorSampler distinguisher ≤
      LearningWithErrors.advantage
        (baseProblem (Row := Row) highSecretSampler highErrorSampler)
        (reductionAdversary (rqDigitExtension p degree) weight lowSecretSampler distinguisher) +
      LearningWithErrors.advantage
        (baseProblem (Row := Row) highSecretSampler highErrorSampler)
        (reductionAdversary (rqDigitExtension p degree) (fun _row : Row ↦ 0)
          lowSecretSampler distinguisher) := by
  exact kdmAdvantage_le_two_base (rqDigitExtension p degree) weight
    lowSecretSampler highSecretSampler highErrorSampler distinguisher hLowSecret

end

end FormalProof4FHE.RLWE.SquareZeroQuadraticCircular
