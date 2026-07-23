/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.Basic
import LatticeCrypto.Ring.Norms
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Vector

/-!
# Cardinality of Finite Centered-Coefficient Support

A polynomial whose centered modular coefficients all have absolute value at most `bound` injects
coefficientwise into the integer box `[-bound, bound]^degree`.  This gives the representation-free
cardinality bound `(2 * bound + 1)^degree` used for native TFHE transformed-error supports.
-/

namespace FormalProof4FHE.FiniteCenteredSupport

noncomputable section

/-- The vector-backed polynomial carrier is equivalent to its coefficient function. -/
def polynomialEquivPi (Coefficient : Type) (degree : ℕ) :
    LatticeCrypto.Poly Coefficient degree ≃ (Fin degree → Coefficient) where
  toFun := LatticeCrypto.Poly.toPi
  invFun := LatticeCrypto.Poly.ofPi
  left_inv := LatticeCrypto.Poly.ofPi_toPi
  right_inv := LatticeCrypto.Poly.toPi_ofPi

/-- Modular polynomials with centered coefficient infinity norm at most `bound`. -/
abbrev BoundedPolynomial (q degree bound : ℕ) [NeZero q] :=
  {value : FormalProof4FHE.RLWE.Rq q degree //
    LatticeCrypto.cInfNorm value ≤ bound}

noncomputable instance instFintypeBoundedPolynomial
    (q degree bound : ℕ) [NeZero q] :
    Fintype (BoundedPolynomial q degree bound) := by
  classical
  exact Fintype.ofFinite _

/-- Encode every centered coefficient in the corresponding finite integer interval. -/
def boundedPolynomialCode
    {q degree bound : ℕ} [NeZero q]
    (value : BoundedPolynomial q degree bound) :
    Fin degree → {coefficient : ℤ // coefficient ∈
      Finset.Icc (-(bound : ℤ)) (bound : ℤ)} :=
  fun coefficient ↦
    ⟨LatticeCrypto.centeredRepr (LatticeCrypto.Poly.toPi value.1 coefficient), by
      rw [Finset.mem_Icc]
      have hcoefficient :
          (LatticeCrypto.centeredRepr
            (LatticeCrypto.Poly.toPi value.1 coefficient)).natAbs ≤ bound :=
        (LatticeCrypto.coeff_le_cInfNorm value.1 coefficient).trans value.2
      constructor <;> omega⟩

theorem boundedPolynomialCode_injective
    {q degree bound : ℕ} [NeZero q] :
    Function.Injective (boundedPolynomialCode :
      BoundedPolynomial q degree bound →
        Fin degree → {coefficient : ℤ // coefficient ∈
          Finset.Icc (-(bound : ℤ)) (bound : ℤ)}) := by
  intro left right heq
  apply Subtype.ext
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  have hcoefficient := congrArg
    (fun encoded ↦ (encoded coefficient).1) heq
  change LatticeCrypto.Poly.toPi left.1 coefficient =
    LatticeCrypto.Poly.toPi right.1 coefficient
  calc
    LatticeCrypto.Poly.toPi left.1 coefficient =
        ((LatticeCrypto.centeredRepr
          (LatticeCrypto.Poly.toPi left.1 coefficient) : ℤ) : ZMod q) :=
      LatticeCrypto.centeredRepr_intCast _
    _ = ((LatticeCrypto.centeredRepr
          (LatticeCrypto.Poly.toPi right.1 coefficient) : ℤ) : ZMod q) := by
      exact congrArg (fun value : ℤ ↦ (value : ZMod q)) hcoefficient
    _ = LatticeCrypto.Poly.toPi right.1 coefficient :=
      (LatticeCrypto.centeredRepr_intCast _).symm

/-- There are at most `(2 * bound + 1)^degree` centered-bounded modular polynomials. -/
theorem card_boundedPolynomial_le
    (q degree bound : ℕ) [NeZero q] :
    Fintype.card (BoundedPolynomial q degree bound) ≤
      (2 * bound + 1) ^ degree := by
  calc
    Fintype.card (BoundedPolynomial q degree bound) ≤
        Fintype.card
          (Fin degree → {coefficient : ℤ // coefficient ∈
            Finset.Icc (-(bound : ℤ)) (bound : ℤ)}) :=
      Fintype.card_le_of_injective boundedPolynomialCode
        boundedPolynomialCode_injective
    _ = (2 * bound + 1) ^ degree := by
      rw [Fintype.card_fun, Fintype.card_fin]
      congr 1
      rw [Fintype.card_coe]
      simp
      omega

end

end FormalProof4FHE.FiniteCenteredSupport
