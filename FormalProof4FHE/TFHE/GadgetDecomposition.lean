/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.Evaluation
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Indexes
import Mathlib.Algebra.BigOperators.Fin

/-!
# Executable Finite-Modulus TFHE Gadget Decomposition

This file supplies a concrete base decomposition for the finite `ZMod q` TFHE model.  A parameter
package records a base `B > 1`, a level count `ell`, and the capacity condition `q ≤ B^ell`.
`Nat.digitsAppend` then gives exactly `ell` little-endian digits for the canonical representative
of every residue.

The checked reconstruction theorem is an equality in `ZMod q`, not an informal integer identity.
It is lifted both to all extended TLWE coordinates and coefficientwise to the executable
negacyclic ring `Rq`.  Thus the same digit algorithm plugs directly into the exact TLWE,
key-switch, and TGSW external-product identities in `TFHE.Evaluation`.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Gadget.Base

/-- Exact unsigned base-decomposition parameters for modulus `q`. -/
structure Parameters (q : ℕ) where
  base : ℕ
  levels : ℕ
  one_lt_base : 1 < base
  modulus_le_capacity : q ≤ base ^ levels

variable {q : ℕ} [NeZero q]

/-- The fixed-length little-endian digit list of the canonical representative of `value`. -/
def digitList (params : Parameters q) (value : ZMod q) : List ℕ :=
  Nat.digitsAppend params.base params.levels value.val

/-- Capacity ensures that the padded digit list has exactly the configured level count. -/
@[simp]
theorem digitList_length (params : Parameters q) (value : ZMod q) :
    (digitList params value).length = params.levels := by
  exact Nat.length_digitsAppend params.one_lt_base params.levels
    (value.val_lt.trans_le params.modulus_le_capacity)

/-- The natural-valued digit at one configured level. -/
def natDigit (params : Parameters q) (value : ZMod q) (level : Fin params.levels) : ℕ :=
  (digitList params value).getD level.val 0

/-- Every unsigned digit is strictly smaller than the configured base. -/
theorem natDigit_lt_base (params : Parameters q) (value : ZMod q)
    (level : Fin params.levels) : natDigit params value level < params.base := by
  have hlevel : level.val < (digitList params value).length := by
    rw [digitList_length]
    exact level.isLt
  let index : Fin (digitList params value).length := ⟨level.val, hlevel⟩
  change (digitList params value).getD index.val 0 < params.base
  rw [List.getD_eq_get (digitList params value) 0 index]
  apply Nat.lt_of_mem_digitsAppend (n := value.val) params.one_lt_base params.levels
  simpa only [digitList] using
    (List.get_mem (l := digitList params value) index)

/-- Cast the natural base digit into the finite coefficient ring. -/
def digit (params : Parameters q) (value : ZMod q) (level : Fin params.levels) : ZMod q :=
  natDigit params value level

/-- The ordinary little-endian power-of-base gadget in `ZMod q`. -/
def gadget (params : Parameters q) (level : Fin params.levels) : ZMod q :=
  params.base ^ level.val

/-- Natural-number reconstruction of the canonical representative from the fixed digit vector. -/
theorem nat_recompose (params : Parameters q) (value : ZMod q) :
    (∑ level : Fin params.levels,
      natDigit params value level * params.base ^ level.val) = value.val := by
  let digits := digitList params value
  have hlength : digits.length = params.levels := digitList_length params value
  have hsum :
      (∑ level : Fin params.levels,
          digits.getD level.val 0 * params.base ^ level.val) =
        ∑ index : Fin digits.length,
          digits.get index * params.base ^ index.val := by
    apply Fintype.sum_equiv (finCongr hlength.symm)
    intro level
    have hlevel : level.val < digits.length := by
      rw [hlength]
      exact level.isLt
    rw [List.getD_eq_getElem _ _ hlevel]
    rfl
  calc
    (∑ level : Fin params.levels,
        natDigit params value level * params.base ^ level.val) =
        ∑ level : Fin params.levels,
          digits.getD level.val 0 * params.base ^ level.val := by
      rfl
    _ = ∑ index : Fin digits.length,
          digits.get index * params.base ^ index.val := hsum
    _ = (digits.mapIdx fun index coefficient ↦
          coefficient * params.base ^ index).sum := by
      rw [List.mapIdx_eq_ofFn, List.sum_ofFn]
    _ = Nat.ofDigits params.base digits := by
      rw [Nat.ofDigits_eq_sum_mapIdx]
    _ = value.val := by
      simp only [digits, digitList, Nat.digitsAppend,
        Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- **Executable scalar recomposition.** The configured digits reconstruct every residue exactly
in `ZMod q`. -/
theorem recompose (params : Parameters q) (value : ZMod q) :
    Gadget.recompose (gadget params) (digit params value) = value := by
  unfold Gadget.recompose gadget digit
  calc
    (∑ level : Fin params.levels,
        (natDigit params value level : ZMod q) *
          (params.base ^ level.val : ZMod q)) =
        ((∑ level : Fin params.levels,
          natDigit params value level * params.base ^ level.val : ℕ) : ZMod q) := by
      norm_cast
    _ = (value.val : ZMod q) := by rw [nat_recompose]
    _ = value := ZMod.natCast_zmod_val value

/-- Decompose every extended TLWE coordinate with the executable scalar digit algorithm. -/
def extendedDigits {dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (ZMod q) dimension) :
    Fin (dimension + 1) → Fin params.levels → ZMod q :=
  fun block ↦ digit params (Gadget.extendedCiphertext ciphertext block)

/-- The executable extended-coordinate digits satisfy the exact TGSW recomposition contract. -/
theorem extendedDigits_decomposes {dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (ZMod q) dimension) :
    Gadget.Decomposes (gadget params) ciphertext (extendedDigits params ciphertext) := by
  intro block
  exact recompose params (Gadget.extendedCiphertext ciphertext block)

/-- Decompose only the source mask coordinates used by key switching. -/
def maskDigits {dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (ZMod q) dimension) :
    Fin dimension → Fin params.levels → ZMod q :=
  fun coordinate ↦ digit params (ciphertext.mask coordinate)

/-- The executable mask digits satisfy the exact key-switch recomposition contract. -/
theorem maskDigits_decomposes {dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (ZMod q) dimension) :
    Gadget.DecomposesMask (gadget params) ciphertext (maskDigits params ciphertext) := by
  intro coordinate
  exact recompose params (ciphertext.mask coordinate)

/-! ## Coefficientwise decomposition in the executable negacyclic ring -/

/-- Apply the scalar digit algorithm independently to every coefficient of an `Rq` element. -/
def ringDigit {degree : ℕ} (params : Parameters q) (value : RLWE.Rq q degree)
    (level : Fin params.levels) : RLWE.Rq q degree :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦
    digit params (LatticeCrypto.Poly.toPi value coefficient) level

/-- The power-of-base gadget embedded as a natural-number constant of `Rq`.  For positive degree
this is the usual constant polynomial; the degree-zero executable carrier is subsingleton. -/
noncomputable def ringGadget {degree : ℕ} (params : Parameters q)
    (level : Fin params.levels) : RLWE.Rq q degree :=
  ((params.base ^ level.val : ℕ) : RLWE.Rq q degree)

omit [NeZero q] in
/-- The level-zero ring gadget is nonzero whenever the coefficient modulus and polynomial degree
are nontrivial.  This is the concrete witness needed to show that a native TGSW mask-block phase
really contains a nonlinear secret product rather than a vacuous zero coordinate. -/
theorem ringGadget_zero_ne_zero {degree : ℕ} [Fact (1 < q)]
    (params : Parameters q) (hdegree : 0 < degree) (hlevels : 0 < params.levels) :
    ringGadget (degree := degree) params ⟨0, hlevels⟩ ≠ 0 := by
  simp only [ringGadget, pow_zero, Nat.cast_one]
  cases degree with
  | zero => omega
  | succ degree =>
      intro hzero
      have hcoefficient := congrArg
        (fun value : RLWE.Rq q (degree + 1) ↦
          LatticeCrypto.Poly.toPi value ⟨0, Nat.succ_pos degree⟩) hzero
      change LatticeCrypto.Poly.toPi
          (LatticeCrypto.vectorNegacyclicRing (ZMod q) (degree + 1)).one
            ⟨0, Nat.succ_pos degree⟩ =
        LatticeCrypto.Poly.toPi
          (LatticeCrypto.vectorNegacyclicRing (ZMod q) (degree + 1)).zero
            ⟨0, Nat.succ_pos degree⟩ at hcoefficient
      simp [LatticeCrypto.Poly.toPi,
        LatticeCrypto.vectorNegacyclicRing, Vector.get] at hcoefficient
      exact one_ne_zero hcoefficient

/-- Coefficient access for the vector-backed ring is additive. -/
def coefficientAddHom (degree : ℕ) (coefficient : Fin degree) :
    RLWE.Rq q degree →+ ZMod q where
  toFun value := (RLWE.negacyclicRing q degree).backend.coeff value coefficient
  map_zero' := by
    cases degree with
    | zero => exact coefficient.elim0
    | succ degree =>
        exact LatticeCrypto.NegacyclicRing.coeff_zero
          (RLWE.negacyclicRing q (degree + 1)) coefficient
  map_add' := by
    intro left right
    cases degree with
    | zero => exact coefficient.elim0
    | succ degree =>
        exact LatticeCrypto.NegacyclicRing.coeff_add
          (RLWE.negacyclicRing q (degree + 1)) left right coefficient

omit [NeZero q] in
@[simp]
theorem coefficientAddHom_apply (degree : ℕ) (coefficient : Fin degree)
    (value : RLWE.Rq q degree) :
    coefficientAddHom degree coefficient value =
      LatticeCrypto.Poly.toPi value coefficient := by
  rfl

omit [NeZero q] in
@[simp]
theorem ringDigit_coefficient {degree : ℕ} (params : Parameters q)
    (value : RLWE.Rq q degree) (level : Fin params.levels) (coefficient : Fin degree) :
    LatticeCrypto.Poly.toPi (ringDigit params value level) coefficient =
      digit params (LatticeCrypto.Poly.toPi value coefficient) level := by
  simp [ringDigit]

omit [NeZero q] in
/-- Multiplication by a gadget constant is repeated addition by the corresponding natural. -/
theorem mul_ringGadget_eq_nsmul {degree : ℕ} (params : Parameters q)
    (value : RLWE.Rq q degree) (level : Fin params.levels) :
    value * ringGadget params level = (params.base ^ level.val) • value := by
  cases degree with
  | zero =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree =>
      unfold ringGadget
      calc
        value * ((params.base ^ level.val : ℕ) : RLWE.Rq q (degree + 1)) =
            ((params.base ^ level.val : ℕ) : RLWE.Rq q (degree + 1)) * value :=
          mul_comm _ _
        _ = (params.base ^ level.val) • value :=
          (nsmul_eq_mul (params.base ^ level.val) value).symm

/-- **Executable ring recomposition.** Coefficientwise scalar digits reconstruct every element of
the concrete negacyclic ring exactly. -/
theorem ring_recompose {degree : ℕ} (params : Parameters q) (value : RLWE.Rq q degree) :
    Gadget.recompose (ringGadget params) (ringDigit params value) = value := by
  cases degree with
  | zero =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      change coefficientAddHom (degree + 1) coefficient
          (Gadget.recompose (ringGadget params) (ringDigit params value)) =
        coefficientAddHom (degree + 1) coefficient value
      unfold Gadget.recompose
      simp_rw [mul_ringGadget_eq_nsmul]
      rw [map_sum]
      simp only [map_nsmul, coefficientAddHom_apply, ringDigit_coefficient]
      change (∑ level : Fin params.levels,
          (params.base ^ level.val) •
            digit params (LatticeCrypto.Poly.toPi value coefficient) level) =
        LatticeCrypto.Poly.toPi value coefficient
      simpa only [Gadget.recompose, gadget, nsmul_eq_mul, Nat.cast_pow, mul_comm] using
        recompose params (LatticeCrypto.Poly.toPi value coefficient)

/-- Decompose every extended coordinate of a TLWE row over `Rq` coefficientwise.  This is the
concrete decomposition consumed by a TGSW--TRLWE external product. -/
def ringExtendedDigits {degree dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (RLWE.Rq q degree) dimension) :
    Fin (dimension + 1) → Fin params.levels → RLWE.Rq q degree :=
  fun block ↦ ringDigit params (Gadget.extendedCiphertext ciphertext block)

/-- The executable ring extended-coordinate digits satisfy the exact TGSW recomposition
contract. -/
theorem ringExtendedDigits_decomposes {degree dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (RLWE.Rq q degree) dimension) :
    Gadget.Decomposes (ringGadget params) ciphertext
      (ringExtendedDigits params ciphertext) := by
  intro block
  exact ring_recompose params (Gadget.extendedCiphertext ciphertext block)

/-- Decompose only the mask coordinates of an `Rq`-valued TLWE row coefficientwise. -/
def ringMaskDigits {degree dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (RLWE.Rq q degree) dimension) :
    Fin dimension → Fin params.levels → RLWE.Rq q degree :=
  fun coordinate ↦ ringDigit params (ciphertext.mask coordinate)

/-- The executable ring mask digits satisfy the exact key-switch recomposition contract. -/
theorem ringMaskDigits_decomposes {degree dimension : ℕ} (params : Parameters q)
    (ciphertext : TLWE.Ciphertext (RLWE.Rq q degree) dimension) :
    Gadget.DecomposesMask (ringGadget params) ciphertext
      (ringMaskDigits params ciphertext) := by
  intro coordinate
  exact ring_recompose params (ciphertext.mask coordinate)

end FormalProof4FHE.TFHE.Gadget.Base
