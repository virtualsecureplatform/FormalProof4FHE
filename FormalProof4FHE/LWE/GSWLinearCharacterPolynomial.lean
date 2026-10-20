/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWLinearCharacterCompiler
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Public polynomial certificates for character-compiler discrepancies

The actual cubic phase has an explicit sparse polynomial over the original
secret coordinates. Its coefficient discrepancy from any public target gives
a supported error bound for EVERY binary secret, without assuming cancellation
or an oracle for the secret. The certificate also permits low gadget levels
whose target is not divisible by four.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWLinearCharacterPolynomial

open GSWLinearCharacterCompiler

noncomputable def cubicPolynomial {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R)
    (u : Matrix P (Fin m) R) : MvPolynomial (Fin n) R :=
  ∑ pair, ∑ row, if row ≠ first pair ∧ row ≠ second pair then
    MvPolynomial.C (4 * projectedMask a u pair row) *
      MvPolynomial.X (first pair) * MvPolynomial.X (second pair) * MvPolynomial.X row
    else 0

theorem eval_cubicPolynomial {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R)
    (u : Matrix P (Fin m) R) (secret : Fin n → R) :
    MvPolynomial.eval secret (cubicPolynomial first second a u) =
      cubicPhase first second a u secret := by
  classical
  simp only [cubicPolynomial, map_sum, cubicPhase, tailPhase, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  apply Finset.sum_congr rfl
  intro row _
  split_ifs
  · simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    ring
  · simp

theorem cubicPolynomial_zero {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R) :
    cubicPolynomial first second a (0 : Matrix P (Fin m) R) = 0 := by
  classical
  simp [cubicPolynomial, projectedMask, mulVec, dotProduct]

theorem cubicPolynomial_three {R : Type} [CommRing R] {m : ℕ}
    (a : Matrix (Fin 3) (Fin m) R) (u : Matrix (Fin 3) (Fin m) R) :
    cubicPolynomial first3 second3 a u = MvPolynomial.C (4 * coefficient3 a u) *
      MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 := by
  simp [cubicPolynomial, first3, second3, coefficient3, Fin.sum_univ_succ]
  ring

theorem binary_monomial {R : Type} [CommRing R] {n : ℕ} (bits : Fin n → Bool)
    (degree : Fin n →₀ ℕ) :
    (∏ row, GSWSelfKey.binaryEmbed (R := R) bits row ^ degree row) = 0 ∨
      (∏ row, GSWSelfKey.binaryEmbed (R := R) bits row ^ degree row) = 1 := by
  classical
  have hp (row : Fin n) : GSWSelfKey.binaryEmbed (R := R) bits row ^ degree row = 0 ∨
      GSWSelfKey.binaryEmbed (R := R) bits row ^ degree row = 1 := by
    cases hb : bits row
    · by_cases hd : degree row = 0 <;> simp [GSWSelfKey.binaryEmbed, hb, hd]
    · simp [GSWSelfKey.binaryEmbed, hb]
  have hs (s : Finset (Fin n)) :
      (∏ row ∈ s, GSWSelfKey.binaryEmbed (R := R) bits row ^ degree row) = 0 ∨
        (∏ row ∈ s, GSWSelfKey.binaryEmbed (R := R) bits row ^ degree row) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert row s hrow ih =>
        rw [Finset.prod_insert hrow]
        rcases hp row with h | h <;> rcases ih with h' | h' <;> simp [h, h']
  exact hs Finset.univ

noncomputable def coefficientBound {q n : ℕ} [NeZero q]
    (polynomial : MvPolynomial (Fin n) (ZMod q)) : ℕ :=
  ∑ degree ∈ polynomial.support, (LatticeCrypto.centeredRepr (polynomial.coeff degree)).natAbs

@[simp] theorem coefficientBound_zero {q n : ℕ} [NeZero q] :
    coefficientBound (0 : MvPolynomial (Fin n) (ZMod q)) = 0 := by
  simp [coefficientBound]

@[simp] theorem coefficientBound_neg {q n : ℕ} [NeZero q]
    (polynomial : MvPolynomial (Fin n) (ZMod q)) :
    coefficientBound (-polynomial) = coefficientBound polynomial := by
  simp only [coefficientBound, MvPolynomial.support_neg, MvPolynomial.coeff_neg,
    LatticeCrypto.centeredRepr_natAbs_neg]

theorem coefficientBound_monomial {q n : ℕ} [NeZero q]
    (degree : Fin n →₀ ℕ) (value : ZMod q) :
    coefficientBound (MvPolynomial.monomial degree value) =
      (LatticeCrypto.centeredRepr value).natAbs := by
  classical
  by_cases h : value = 0
  · simp [h, coefficientBound, LatticeCrypto.centeredRepr_eq_valMinAbs]
  · simp [coefficientBound, MvPolynomial.support_monomial, h, MvPolynomial.coeff_monomial]

theorem coefficientBound_cubicMonomial {q n : ℕ} [NeZero q]
    (i j k : Fin n) (value : ZMod q) :
    coefficientBound (MvPolynomial.C value * MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X k) =
      (LatticeCrypto.centeredRepr value).natAbs := by
  rw [MvPolynomial.C_mul_X_eq_monomial]
  simp only [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one]
  exact coefficientBound_monomial _ _

/-- A public coefficient bound for all binary secrets, including all correlations. -/
theorem eval_binary_bound {q n : ℕ} [NeZero q]
    (polynomial : MvPolynomial (Fin n) (ZMod q)) (bits : Fin n → Bool) :
    (LatticeCrypto.centeredRepr
      (MvPolynomial.eval (GSWSelfKey.binaryEmbed bits) polynomial)).natAbs ≤
      coefficientBound polynomial := by
  classical
  rw [MvPolynomial.eval_eq']
  apply (TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _).trans
  apply Finset.sum_le_sum
  intro degree _
  rcases binary_monomial (R := ZMod q) bits degree with h | h
  · simp [h, LatticeCrypto.centeredRepr_eq_valMinAbs]
  · simp only [h, mul_one, le_refl]

theorem cubic_discrepancy_bound {q n m : ℕ} [NeZero q] {P : Type} [Fintype P]
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) (ZMod q))
    (u : Matrix P (Fin m) (ZMod q)) (target : MvPolynomial (Fin n) (ZMod q))
    (bits : Fin n → Bool) :
    (LatticeCrypto.centeredRepr
      (cubicPhase first second a u (GSWSelfKey.binaryEmbed bits) -
        MvPolynomial.eval (GSWSelfKey.binaryEmbed bits) target)).natAbs ≤
      coefficientBound (cubicPolynomial first second a u - target) := by
  have h := eval_binary_bound (cubicPolynomial first second a u - target) bits
  simpa only [map_sub, eval_cubicPolynomial] using h

end FormalProof4FHE.LWE.GSWLinearCharacterPolynomial
