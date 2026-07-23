/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.GadgetDecomposition
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Exact Uniformity of Full-Capacity Gadget Digits

When the coefficient modulus is exactly `base ^ levels`, the executable unsigned gadget
decomposition is not merely reconstructing: it is a bijection from residues to complete fixed
length base-digit vectors.  Therefore decomposing a uniform residue gives mutually independent
uniform digits exactly.  This module proves the scalar statement and its coefficientwise lift to
the executable negacyclic ring.

These facts supply the exact input law needed for quantitative analysis of the native TFHE
identity-plus-digit determinant event.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Gadget.Base

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Every valid gadget base is nonzero, making its finite digit alphabet sampleable. -/
instance paramsBaseNeZero (params : Parameters q) : NeZero params.base :=
  ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one params.one_lt_base)⟩

/-- The natural digits of one residue, with their range proof retained in the type. -/
def digitVector (params : Parameters q) (value : ZMod q) :
    Fin params.levels → Fin params.base :=
  fun level => ⟨natDigit params value level, natDigit_lt_base params value level⟩

@[simp]
theorem digitVector_val (params : Parameters q) (value : ZMod q)
    (level : Fin params.levels) :
    (digitVector params value level).val = natDigit params value level :=
  rfl

/-- Exact recomposition makes the complete fixed-length digit vector injective for every valid
capacity parameter package. -/
theorem digitVector_injective (params : Parameters q) :
    Function.Injective (digitVector params) := by
  intro left right heq
  apply ZMod.val_injective
  rw [← nat_recompose params left, ← nat_recompose params right]
  apply Finset.sum_congr rfl
  intro level _
  have hlevel := congrFun heq level
  have hval := congrArg Fin.val hlevel
  simpa only [digitVector_val] using congrArg
    (fun digit => digit * params.base ^ level.val) hval

/-- At exact capacity, scalar gadget decomposition is a bijection onto all base-digit vectors. -/
theorem digitVector_bijective (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    Function.Bijective (digitVector params) := by
  apply (Fintype.bijective_iff_injective_and_card (digitVector params)).2
  refine ⟨digitVector_injective params, ?_⟩
  simp [hcapacity]

/-- Equivalence form of exact-capacity scalar gadget decomposition. -/
noncomputable def digitEquiv (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    ZMod q ≃ (Fin params.levels → Fin params.base) :=
  Equiv.ofBijective (digitVector params) (digitVector_bijective params hcapacity)

/-- Decomposing a uniform residue at exact capacity gives the complete uniform digit-vector law
exactly, hence gives independent uniform base digits. -/
theorem digitVector_uniform_evalDist (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    evalDist (digitVector params <$> ($ᵗ ZMod q)) =
      evalDist ($ᵗ (Fin params.levels → Fin params.base)) :=
  evalDist_map_bijective_uniform_cross
    (α := ZMod q) (β := Fin params.levels → Fin params.base)
    (digitVector params) (digitVector_bijective params hcapacity)

/-! ## Coefficientwise ring lift -/

/-- Coefficient-vector presentation of the executable negacyclic carrier. -/
def rqCoefficientEquiv (degree : ℕ) :
    RLWE.Rq q degree ≃ (Fin degree → ZMod q) where
  toFun := LatticeCrypto.Poly.toPi
  invFun := LatticeCrypto.Poly.ofPi
  left_inv := LatticeCrypto.Poly.ofPi_toPi
  right_inv := LatticeCrypto.Poly.toPi_ofPi

/-- Cardinality of the executable negacyclic carrier. -/
theorem card_rq (degree : ℕ) :
    Fintype.card (RLWE.Rq q degree) = q ^ degree := by
  calc
    Fintype.card (RLWE.Rq q degree) = Fintype.card (Fin degree → ZMod q) :=
      Fintype.card_congr (rqCoefficientEquiv degree)
    _ = q ^ degree := by simp

/-- All base digits of all coefficients of one executable ring element. -/
def ringCoefficientDigitVector {degree : ℕ} (params : Parameters q)
    (value : RLWE.Rq q degree) :
    Fin degree → Fin params.levels → Fin params.base :=
  fun coefficient =>
    digitVector params (LatticeCrypto.Poly.toPi value coefficient)

/-- The finite digit-vector entry casts to the corresponding coefficient of the executable ring
digit. -/
theorem ringCoefficientDigitVector_cast {degree : ℕ} (params : Parameters q)
    (value : RLWE.Rq q degree) (coefficient : Fin degree)
    (level : Fin params.levels) :
    ((ringCoefficientDigitVector params value coefficient level).val : ZMod q) =
      LatticeCrypto.Poly.toPi (ringDigit params value level) coefficient := by
  simp [ringCoefficientDigitVector, digitVector, digit, ringDigit_coefficient]

/-- Coefficientwise complete digit vectors determine the original ring element. -/
theorem ringCoefficientDigitVector_injective {degree : ℕ} (params : Parameters q) :
    Function.Injective (ringCoefficientDigitVector (degree := degree) params) := by
  intro left right heq
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  apply digitVector_injective params
  funext level
  exact congrFun (congrFun heq coefficient) level

/-- At exact capacity, coefficientwise ring decomposition is a bijection onto the complete tensor
of independent base digits. -/
theorem ringCoefficientDigitVector_bijective {degree : ℕ} (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    Function.Bijective (ringCoefficientDigitVector (degree := degree) params) := by
  apply (Fintype.bijective_iff_injective_and_card
    (ringCoefficientDigitVector (degree := degree) params)).2
  refine ⟨ringCoefficientDigitVector_injective params, ?_⟩
  rw [card_rq]
  calc
    q ^ degree = (params.base ^ params.levels) ^ degree :=
      congrArg (fun modulus => modulus ^ degree) hcapacity
    _ = Fintype.card (Fin degree → Fin params.levels → Fin params.base) := by
      simp

/-- Equivalence form of exact-capacity coefficientwise ring decomposition. -/
noncomputable def ringCoefficientDigitEquiv {degree : ℕ} (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    RLWE.Rq q degree ≃
      (Fin degree → Fin params.levels → Fin params.base) :=
  Equiv.ofBijective (ringCoefficientDigitVector params)
    (ringCoefficientDigitVector_bijective params hcapacity)

/-- A uniform negacyclic ring element decomposes exactly to the uniform tensor of coefficient
digits. -/
theorem ringCoefficientDigitVector_uniform_evalDist {degree : ℕ}
    (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    evalDist
        (ringCoefficientDigitVector params <$> ($ᵗ RLWE.Rq q degree)) =
      evalDist
        ($ᵗ (Fin degree → Fin params.levels → Fin params.base)) :=
  evalDist_map_bijective_uniform_cross
    (α := RLWE.Rq q degree)
    (β := Fin degree → Fin params.levels → Fin params.base)
    (ringCoefficientDigitVector params)
    (ringCoefficientDigitVector_bijective params hcapacity)

end

end FormalProof4FHE.TFHE.Gadget.Base
