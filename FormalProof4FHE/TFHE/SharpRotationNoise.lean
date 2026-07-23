/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NoiseBounds

/-!
# Sharp Native Rotation Noise Bounds

Native TFHE rotation factors are signed monomials in the negacyclic ring.  Multiplication by one
of them is a signed permutation of coefficients, so it preserves centered coefficient infinity
norm.  This module proves that fact directly for the executable schoolbook backend.  It also
records the sharper `N * ‖f‖∞ * ‖g‖∞` generic convolution bound obtained by counting the unique
right input coordinate contributing to each fixed left coordinate and output coordinate, lifts
that estimate to the digit-weighted external-product error, and proves the sparse
`(X^a - 1)` factor costs at most `2 * ‖f‖∞`.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.SharpRotationNoise

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- For a fixed left coefficient and output coefficient, the unique right coefficient whose
negacyclic convolution contribution lands at that output. -/
def sourceIndex {degree : ℕ}
    (left output : Fin (degree + 1)) : Fin (degree + 1) :=
  if hle : left.val ≤ output.val then
    ⟨output.val - left.val, by omega⟩
  else
    ⟨output.val + (degree + 1) - left.val, by omega⟩

theorem sourceIndex_val_of_le {degree : ℕ}
    (left output : Fin (degree + 1)) (hle : left.val ≤ output.val) :
    (sourceIndex left output).val = output.val - left.val := by
  simp [sourceIndex, hle]

theorem sourceIndex_val_of_not_le {degree : ℕ}
    (left output : Fin (degree + 1)) (hle : ¬left.val ≤ output.val) :
    (sourceIndex left output).val =
      output.val + (degree + 1) - left.val := by
  simp [sourceIndex, hle]

/-- The selected pair lands at the requested output modulo the negacyclic degree. -/
theorem add_sourceIndex_mod {degree : ℕ}
    (left output : Fin (degree + 1)) :
    (left.val + (sourceIndex left output).val) % (degree + 1) = output.val := by
  by_cases hle : left.val ≤ output.val
  · rw [sourceIndex_val_of_le left output hle]
    have heq : left.val + (output.val - left.val) = output.val := by omega
    rw [heq, Nat.mod_eq_of_lt output.isLt]
  · rw [sourceIndex_val_of_not_le left output hle]
    have heq : left.val + (output.val + (degree + 1) - left.val) =
        output.val + (degree + 1) := by omega
    rw [heq, Nat.add_mod, Nat.mod_eq_of_lt output.isLt, Nat.mod_self]
    simp [Nat.mod_eq_of_lt output.isLt]

/-- The selected convolution pair wraps exactly when the left coordinate lies after the output
coordinate. -/
theorem add_sourceIndex_lt_iff {degree : ℕ}
    (left output : Fin (degree + 1)) :
    left.val + (sourceIndex left output).val < degree + 1 ↔
      left.val ≤ output.val := by
  by_cases hle : left.val ≤ output.val
  · rw [sourceIndex_val_of_le left output hle]
    constructor <;> intro
    · exact hle
    · omega
  · rw [sourceIndex_val_of_not_le left output hle]
    constructor
    · intro hlt
      omega
    · intro h
      exact (hle h).elim

/-- Uniqueness of the right coordinate landing at a fixed output. -/
theorem eq_sourceIndex_of_add_mod_eq {degree : ℕ}
    (left right output : Fin (degree + 1))
    (hmod : (left.val + right.val) % (degree + 1) = output.val) :
    right = sourceIndex left output := by
  apply Fin.ext
  by_cases hle : left.val ≤ output.val
  · rw [sourceIndex_val_of_le left output hle]
    by_cases hsum : left.val + right.val < degree + 1
    · rw [Nat.mod_eq_of_lt hsum] at hmod
      omega
    · have hdegree : degree + 1 ≤ left.val + right.val := Nat.le_of_not_gt hsum
      have hreduced : left.val + right.val - (degree + 1) < degree + 1 := by
        omega
      rw [Nat.mod_eq_sub_mod hdegree, Nat.mod_eq_of_lt hreduced] at hmod
      omega
  · rw [sourceIndex_val_of_not_le left output hle]
    by_cases hsum : left.val + right.val < degree + 1
    · rw [Nat.mod_eq_of_lt hsum] at hmod
      omega
    · have hdegree : degree + 1 ≤ left.val + right.val := Nat.le_of_not_gt hsum
      have hreduced : left.val + right.val - (degree + 1) < degree + 1 := by
        omega
      rw [Nat.mod_eq_sub_mod hdegree, Nat.mod_eq_of_lt hreduced] at hmod
      omega

/-- Reindex the executable double convolution sum by its unique right source coordinate. -/
theorem negacyclicConvCoeff_eq_sum_source
    {R : Type} [CommRing R] {degree : ℕ}
    (left right : Fin (degree + 1) → R) (output : Fin (degree + 1)) :
    LatticeCrypto.negacyclicConvCoeff left right output =
      ∑ input : Fin (degree + 1),
        if input.val ≤ output.val then
          left input * right (sourceIndex input output)
        else
          -(left input * right (sourceIndex input output)) := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro input _
  rw [Finset.sum_eq_single (sourceIndex input output)]
  · rw [if_pos (add_sourceIndex_mod input output)]
    by_cases hle : input.val ≤ output.val
    · rw [if_pos ((add_sourceIndex_lt_iff input output).2 hle), if_pos hle]
    · rw [if_neg (not_congr (add_sourceIndex_lt_iff input output) |>.mpr hle), if_neg hle]
  · intro other _ hne
    have hmod :
        (input.val + other.val) % (degree + 1) ≠ output.val := by
      intro heq
      exact hne (eq_sourceIndex_of_add_mod_eq input other output heq)
    rw [if_neg hmod]
  · simp

/-- The executable negacyclic convolution has only `N`, rather than `N²`, contributing products
at each output coefficient. -/
theorem cInfNorm_mul_le_linear {q degree : ℕ} [NeZero q]
    (left right : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm (left * right) ≤
      (degree + 1) *
        (LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right) := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro output
  rw [show (left * right).get output =
      LatticeCrypto.negacyclicConvCoeff
        (LatticeCrypto.Poly.toPi left) (LatticeCrypto.Poly.toPi right) output by
    exact NoiseBounds.mul_coefficient left right output]
  rw [negacyclicConvCoeff_eq_sum_source]
  let term : Fin (degree + 1) → ZMod q := fun input ↦
    if input.val ≤ output.val then
      left.get input * right.get (sourceIndex input output)
    else
      -(left.get input * right.get (sourceIndex input output))
  have hterm (input : Fin (degree + 1)) :
      (LatticeCrypto.centeredRepr (term input)).natAbs ≤
        LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right := by
    dsimp only [term]
    split_ifs
    · exact (NoiseBounds.centeredRepr_mul_natAbs_le
        (left.get input) (right.get (sourceIndex input output))).trans
          (Nat.mul_le_mul
            (LatticeCrypto.coeff_le_cInfNorm left input)
            (LatticeCrypto.coeff_le_cInfNorm right (sourceIndex input output)))
    · rw [LatticeCrypto.centeredRepr_natAbs_neg]
      exact (NoiseBounds.centeredRepr_mul_natAbs_le
        (left.get input) (right.get (sourceIndex input output))).trans
          (Nat.mul_le_mul
            (LatticeCrypto.coeff_le_cInfNorm left input)
            (LatticeCrypto.coeff_le_cInfNorm right (sourceIndex input output)))
  change (LatticeCrypto.centeredRepr (∑ input, term input)).natAbs ≤ _
  calc
    (LatticeCrypto.centeredRepr (∑ input, term input)).natAbs ≤
        ∑ input, (LatticeCrypto.centeredRepr (term input)).natAbs := by
      simpa using NoiseBounds.centeredRepr_finset_sum_natAbs_le term Finset.univ
    _ ≤ ∑ _input : Fin (degree + 1),
        LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right :=
      Finset.sum_le_sum fun input _ ↦ hterm input
    _ = (degree + 1) *
        (LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right) := by
      simp

/-! ## Linear external-product bounds -/

/-- The digit-weighted row-error term of one TGSW external product uses the linear executable
convolution bound.  This removes one factor of the ring degree from the initial schoolbook
estimate while retaining a deterministic worst-case sum over all gadget rows. -/
theorem cInfNorm_externalProductError_le_linear
    {q degree dimension levels : ℕ} [NeZero q]
    (secret : Fin dimension → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (message : RLWE.Rq q (degree + 1))
    (digits : Fin (dimension + 1) → Fin levels → RLWE.Rq q (degree + 1))
    (ciphertext : TGSW.Ciphertext (RLWE.Rq q (degree + 1)) dimension levels)
    (digitBound rowErrorBound : ℕ)
    (hdigits : ∀ block level,
      LatticeCrypto.cInfNorm (digits block level) ≤ digitBound)
    (hrows : ∀ index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret gadget message ciphertext index) ≤
        rowErrorBound) :
    LatticeCrypto.cInfNorm
        (TGSW.externalProductError (R := RLWE.Rq q (degree + 1))
          secret gadget message digits ciphertext) ≤
      ((dimension + 1) * levels) *
        ((degree + 1) * (digitBound * rowErrorBound)) := by
  unfold TGSW.externalProductError
  calc
    LatticeCrypto.cInfNorm
        (@Finset.sum (Fin (dimension + 1) × Fin levels)
          (RLWE.Rq q (degree + 1)) NoiseBounds.positiveRqRing.toAddCommMonoid Finset.univ
          (fun index ↦ digits index.1 index.2 *
            TGSW.rowError (R := RLWE.Rq q (degree + 1))
              secret gadget message ciphertext index)) ≤
        ∑ index : Fin (dimension + 1) × Fin levels,
          LatticeCrypto.cInfNorm
            (digits index.1 index.2 *
              TGSW.rowError (R := RLWE.Rq q (degree + 1))
                secret gadget message ciphertext index) := by
      simpa using NoiseBounds.cInfNorm_finset_sum_le
        (fun index : Fin (dimension + 1) × Fin levels ↦
          digits index.1 index.2 *
            TGSW.rowError (R := RLWE.Rq q (degree + 1))
              secret gadget message ciphertext index)
        Finset.univ
    _ ≤ ∑ _index : Fin (dimension + 1) × Fin levels,
        (degree + 1) * (digitBound * rowErrorBound) := by
      apply Finset.sum_le_sum
      intro index _
      exact (cInfNorm_mul_le_linear (digits index.1 index.2)
        (TGSW.rowError (R := RLWE.Rq q (degree + 1))
          secret gadget message ciphertext index)).trans
          (Nat.mul_le_mul_left _
            (Nat.mul_le_mul (hdigits index.1 index.2) (hrows index)))
    _ = ((dimension + 1) * levels) *
        ((degree + 1) * (digitBound * rowErrorBound)) := by
      simp [Fintype.card_prod]

/-- Linear external-product bound specialized to the checked executable base digits. -/
theorem cInfNorm_externalProductError_ringDigits_le_linear
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
        ((degree + 1) * ((params.base - 1) * rowErrorBound)) := by
  apply cInfNorm_externalProductError_le_linear secret
    (Gadget.Base.ringGadget params) message
    (Gadget.Base.ringExtendedDigits params input) ciphertext
    (params.base - 1) rowErrorBound
  · intro block level
    exact NoiseBounds.cInfNorm_ringDigit_le params
      (Gadget.extendedCiphertext input block) level
  · exact hrows

/-- The unique nonzero coefficient coordinate of a native signed rotation monomial. -/
def rotationIndex {degree : ℕ}
    (exponent : Fin (2 * (degree + 1))) : Fin (degree + 1) :=
  if hfirst : exponent.val < degree + 1 then
    ⟨exponent.val, hfirst⟩
  else
    ⟨exponent.val - (degree + 1), by omega⟩

theorem rotationIndex_val_of_lt {degree : ℕ}
    (exponent : Fin (2 * (degree + 1)))
    (hfirst : exponent.val < degree + 1) :
    (rotationIndex exponent).val = exponent.val := by
  simp [rotationIndex, hfirst]

theorem rotationIndex_val_of_not_lt {degree : ℕ}
    (exponent : Fin (2 * (degree + 1)))
    (hfirst : ¬exponent.val < degree + 1) :
    (rotationIndex exponent).val = exponent.val - (degree + 1) := by
  simp [rotationIndex, hfirst]

theorem rotationMonomial_coefficient_rotationIndex {q degree : ℕ}
    (exponent : Fin (2 * (degree + 1))) :
    LatticeCrypto.Poly.toPi
        (BlindRotation.rotationMonomial q degree exponent) (rotationIndex exponent) =
      if exponent.val < degree + 1 then 1 else -1 := by
  rw [BlindRotation.rotationMonomial_coefficient]
  by_cases hfirst : exponent.val < degree + 1
  · simp [hfirst, rotationIndex_val_of_lt exponent hfirst]
  · simp [hfirst, rotationIndex_val_of_not_lt exponent hfirst]

theorem rotationMonomial_coefficient_eq_zero_of_ne {q degree : ℕ}
    (exponent : Fin (2 * (degree + 1))) (input : Fin (degree + 1))
    (hne : input ≠ rotationIndex exponent) :
    LatticeCrypto.Poly.toPi
        (BlindRotation.rotationMonomial q degree exponent) input = 0 := by
  rw [BlindRotation.rotationMonomial_coefficient]
  by_cases hfirst : exponent.val < degree + 1
  · have hval : input.val ≠ exponent.val := by
      intro heq
      apply hne
      apply Fin.ext
      rw [rotationIndex_val_of_lt exponent hfirst]
      exact heq
    simp [hfirst, hval]
  · have hval : input.val ≠ exponent.val - (degree + 1) := by
      intro heq
      apply hne
      apply Fin.ext
      rw [rotationIndex_val_of_not_lt exponent hfirst]
      exact heq
    simp [hfirst, hval]

/-- Multiplication by a native signed rotation is a coefficient permutation with possible sign
changes, hence it does not increase centered coefficient infinity norm. -/
theorem cInfNorm_rotationMonomial_mul_le {q degree : ℕ} [NeZero q]
    (exponent : Fin (2 * (degree + 1)))
    (value : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm
        (BlindRotation.rotationMonomial q degree exponent * value) ≤
      LatticeCrypto.cInfNorm value := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro output
  rw [show
      (BlindRotation.rotationMonomial q degree exponent * value).get output =
        LatticeCrypto.negacyclicConvCoeff
          (LatticeCrypto.Poly.toPi
            (BlindRotation.rotationMonomial q degree exponent))
          (LatticeCrypto.Poly.toPi value) output by
    exact NoiseBounds.mul_coefficient
      (BlindRotation.rotationMonomial q degree exponent) value output]
  rw [negacyclicConvCoeff_eq_sum_source]
  rw [Finset.sum_eq_single (rotationIndex exponent)]
  · rw [rotationMonomial_coefficient_rotationIndex]
    by_cases hwrap : (rotationIndex exponent).val ≤ output.val <;>
      by_cases hfirst : exponent.val < degree + 1 <;>
      simp only [hwrap, hfirst, if_true, if_false, one_mul, neg_one_mul, neg_neg,
        LatticeCrypto.centeredRepr_natAbs_neg] <;>
      exact LatticeCrypto.coeff_le_cInfNorm value
        (sourceIndex (rotationIndex exponent) output)
  · intro input _ hne
    rw [rotationMonomial_coefficient_eq_zero_of_ne exponent input hne]
    simp
  · simp

/-- Multiplying by `X^a - 1` costs at most two copies of the input norm.  Expanding the
difference first avoids applying a generic convolution estimate to the sparse public factor. -/
theorem cInfNorm_rotationMonomial_sub_one_mul_le_two
    {q degree : ℕ} [NeZero q]
    (exponent : Fin (2 * (degree + 1)))
    (value : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm
        ((BlindRotation.rotationMonomial q degree exponent - 1) * value) ≤
      2 * LatticeCrypto.cInfNorm value := by
  have hsplit :
      (BlindRotation.rotationMonomial q degree exponent - 1) * value =
        BlindRotation.rotationMonomial q degree exponent * value - value := by
    ring
  calc
    LatticeCrypto.cInfNorm
        ((BlindRotation.rotationMonomial q degree exponent - 1) * value) =
        LatticeCrypto.cInfNorm
          (BlindRotation.rotationMonomial q degree exponent * value - value) :=
      congrArg LatticeCrypto.cInfNorm hsplit
    LatticeCrypto.cInfNorm
        (BlindRotation.rotationMonomial q degree exponent * value - value) ≤
        LatticeCrypto.cInfNorm
            (BlindRotation.rotationMonomial q degree exponent * value) +
          LatticeCrypto.cInfNorm value :=
      NoiseBounds.cInfNorm_sub_le
        (BlindRotation.rotationMonomial q degree exponent * value) value
    _ ≤ LatticeCrypto.cInfNorm value + LatticeCrypto.cInfNorm value :=
      Nat.add_le_add_right (cInfNorm_rotationMonomial_mul_le exponent value) _
    _ = 2 * LatticeCrypto.cInfNorm value := by omega

/-- A product of native signed-rotation selectors acts on any value by successive signed
coefficient permutations.  Its action therefore cannot increase infinity norm, without first
expanding the product or paying a convolution factor. -/
theorem cInfNorm_idealMultiplier_mul_le
    {q degree rank levels : ℕ} [NeZero q]
    (controls : List (BlindRotation.BitControl q degree rank levels))
    (hrotation : ∀ control ∈ controls,
      ∃ exponent : Fin (2 * (degree + 1)),
        control.factor = BlindRotation.rotationMonomial q degree exponent)
    (value : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm
        (BlindRotation.idealMultiplier controls * value) ≤
      LatticeCrypto.cInfNorm value := by
  induction controls generalizing value with
  | nil =>
      simp [BlindRotation.idealMultiplier]
  | cons control controls ih =>
      have hhead := hrotation control (by simp)
      obtain ⟨exponent, hfactor⟩ := hhead
      have htail : ∀ item ∈ controls,
          ∃ itemExponent : Fin (2 * (degree + 1)),
            item.factor =
              BlindRotation.rotationMonomial q degree itemExponent := by
        intro item hmem
        exact hrotation item (by simp [hmem])
      calc
        LatticeCrypto.cInfNorm
            (BlindRotation.idealMultiplier (control :: controls) * value) =
            LatticeCrypto.cInfNorm
              (BlindRotation.idealMultiplier controls *
                ((if control.bit then control.factor else 1) * value)) := by
              congr 1
              simp only [BlindRotation.idealMultiplier]
              rw [mul_assoc]
        _ ≤ LatticeCrypto.cInfNorm
              ((if control.bit then control.factor else 1) * value) :=
            ih htail _
        _ ≤ LatticeCrypto.cInfNorm value := by
          cases hbit : control.bit
          · simp
          · simpa [hfactor] using
              cInfNorm_rotationMonomial_mul_le exponent value

end

end FormalProof4FHE.TFHE.SharpRotationNoise
