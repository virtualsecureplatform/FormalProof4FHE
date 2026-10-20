/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWQuadraticPreimageRowSupport
import FormalProof4FHE.LWE.RecursiveQuadratic

/-!
# A public cubic compiler with linear source error

Quadratic Boolean characters multiply public linear projections of ordinary
LWE bodies. Public quadratic corrections remove the lower-degree terms.
The resulting original-key phase is an explicit cubic form plus a LINEAR
source-error sum. All ciphertext coordinates are constructed publicly.

The coefficient builder's family shortness and complete-view security remain
unproved. No such premise is added as a cryptographic assumption here.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWLinearCharacterCompiler

def character {R : Type} [CommRing R] (value : R) : R := 2 * value - 1

def pairPolynomial {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (value : R) :
    RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ row column ↦ if row = i ∧ column = j then 4 * value else 0
  linear := fun _ row ↦ (if row = i then -2 * value else 0) +
    (if row = j then -2 * value else 0)
  constant := fun _ ↦ value

theorem message_pairPolynomial {R : Type} [CommRing R] {n : ℕ}
    (i j : Fin n) (value : R) (secret : Fin n → R) :
    RecursiveQuadratic.message (pairPolynomial i j value) secret 0 =
      character (secret i) * character (secret j) * value := by
  simp only [RecursiveQuadratic.message, pairPolynomial, vecMul, dotProduct, ite_and,
    add_mul, mul_ite, ite_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, zero_mul,
    character]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

def lowerPolynomial {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (a : Fin n → R) :
    RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ row column ↦ (if row = i then -2 * a column else 0) +
    (if row = j then -2 * a column else 0) +
    (if row = i ∧ column = j then 4 * (a i + a j) else 0)
  linear := fun _ ↦ a
  constant := fun _ ↦ 0

theorem message_lowerPolynomial {R : Type} [CommRing R] {n : ℕ}
    (i j : Fin n) (a secret : Fin n → R) :
    RecursiveQuadratic.message (lowerPolynomial i j a) secret 0 =
      dotProduct a secret - 2 * secret i * dotProduct a secret -
        2 * secret j * dotProduct a secret + 4 * (a i + a j) * secret i * secret j := by
  simp only [RecursiveQuadratic.message, lowerPolynomial, vecMul, dotProduct, ite_and,
    mul_add, add_mul, mul_ite, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.mul_sum, mul_neg, neg_mul, Finset.sum_neg_distrib]
  ring_nf

def tailPhase {R : Type} [CommRing R] {n : ℕ}
    (i j : Fin n) (a secret : Fin n → R) : R :=
  ∑ row, if row ≠ i ∧ row ≠ j then a row * secret row else 0

theorem dotProduct_split {R : Type} [CommRing R] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (a secret : Fin n → R) :
    dotProduct a secret = a i * secret i + a j * secret j + tailPhase i j a secret := by
  have hpoint : ∀ row, a row * secret row =
      (if row = i then a i * secret i else 0) +
      (if row = j then a j * secret j else 0) +
      (if row ≠ i ∧ row ≠ j then a row * secret row else 0) := by
    intro row
    by_cases hi : row = i
    · subst row; simp [hij]
    · by_cases hj : row = j
      · subst row; simp [Ne.symm hij]
      · simp [hi, hj]
  calc
    _ = ∑ row, ((if row = i then a i * secret i else 0) +
        (if row = j then a j * secret j else 0) +
        (if row ≠ i ∧ row ≠ j then a row * secret row else 0)) :=
      Finset.sum_congr rfl (fun row _ ↦ hpoint row)
    _ = _ := by simp [Finset.sum_add_distrib, tailPhase]

theorem character_lower_identity {R : Type} [CommRing R] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (a secret : Fin n → R)
    (hi : secret i * secret i = secret i) (hj : secret j * secret j = secret j) :
    character (secret i) * character (secret j) * dotProduct a secret -
      RecursiveQuadratic.message (lowerPolynomial i j a) secret 0 =
      4 * secret i * secret j * tailPhase i j a secret := by
  rw [message_lowerPolynomial, dotProduct_split i j hij]
  unfold character
  linear_combination 4 * a i * secret j * hi + 4 * a j * secret i * hj

def projectedMask {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (u : Matrix P (Fin m) R) (pair : P) : Fin n → R :=
  a.mulVec (u pair)

def subPolynomial {R : Type} [CommRing R] {n : ℕ}
    (a b : RecursiveQuadratic.Polynomial R n 1) : RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ row column ↦ a.quadratic 0 row column - b.quadratic 0 row column
  linear := fun _ row ↦ a.linear 0 row - b.linear 0 row
  constant := fun _ ↦ a.constant 0 - b.constant 0

theorem message_subPolynomial {R : Type} [CommRing R] {n : ℕ}
    (a b : RecursiveQuadratic.Polynomial R n 1) (secret : Fin n → R) :
    RecursiveQuadratic.message (subPolynomial a b) secret 0 =
      RecursiveQuadratic.message a secret 0 - RecursiveQuadratic.message b secret 0 := by
  simp only [RecursiveQuadratic.message, subPolynomial, vecMul, dotProduct,
    mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

def sumPolynomial {R P : Type} [CommRing R] [Fintype P] {n : ℕ}
    (p : P → RecursiveQuadratic.Polynomial R n 1) : RecursiveQuadratic.Polynomial R n 1 where
  quadratic := fun _ row column ↦ ∑ pair, (p pair).quadratic 0 row column
  linear := fun _ row ↦ ∑ pair, (p pair).linear 0 row
  constant := fun _ ↦ ∑ pair, (p pair).constant 0

theorem message_sumPolynomial {R P : Type} [CommRing R] [Fintype P] {n : ℕ}
    (p : P → RecursiveQuadratic.Polynomial R n 1) (secret : Fin n → R) :
    RecursiveQuadratic.message (sumPolynomial p) secret 0 =
      ∑ pair, RecursiveQuadratic.message (p pair) secret 0 := by
  have hquad : (∑ column : Fin n, ∑ row : Fin n, ∑ pair : P,
      secret row * (p pair).quadratic 0 row column * secret column) =
      ∑ pair : P, ∑ column : Fin n, ∑ row : Fin n,
        secret row * (p pair).quadratic 0 row column * secret column := by
    calc
      _ = ∑ column : Fin n, ∑ pair : P, ∑ row : Fin n,
          secret row * (p pair).quadratic 0 row column * secret column := by
        apply Finset.sum_congr rfl
        intro column _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hlinear : (∑ row : Fin n, ∑ pair : P, (p pair).linear 0 row * secret row) =
      ∑ pair : P, ∑ row : Fin n, (p pair).linear 0 row * secret row := Finset.sum_comm
  simp only [RecursiveQuadratic.message, sumPolynomial, vecMul, dotProduct,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
  rw [hquad, hlinear]

def polynomial {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R)
    (u : Matrix P (Fin m) R) (bodies : Fin m → R) : RecursiveQuadratic.Polynomial R n 1 :=
  sumPolynomial fun pair ↦ subPolynomial
    (pairPolynomial (first pair) (second pair) (dotProduct (u pair) bodies))
    (lowerPolynomial (first pair) (second pair) (projectedMask a u pair))

def compile {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R)
    (u : Matrix P (Fin m) R) (bodies : Fin m → R) : RecursiveQuadratic.Ciphertext R n :=
  let p := polynomial first second a u bodies
  (-p.quadratic 0, p.linear 0, p.constant 0)

theorem decrypt_compile {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R)
    (u : Matrix P (Fin m) R) (bodies : Fin m → R) (secret : Fin n → R) :
    RecursiveQuadratic.decrypt secret (compile first second a u bodies) =
      ∑ pair, (character (secret (first pair)) * character (secret (second pair)) *
        dotProduct (u pair) bodies -
          RecursiveQuadratic.message (lowerPolynomial (first pair) (second pair) (projectedMask a u pair)) secret 0) := by
  have hphase : RecursiveQuadratic.decrypt secret (compile first second a u bodies) =
      RecursiveQuadratic.message (polynomial first second a u bodies) secret 0 := by
    simp only [RecursiveQuadratic.decrypt, compile, RecursiveQuadratic.message,
      vecMul, dotProduct, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [hphase]
  unfold polynomial
  rw [message_sumPolynomial]
  simp_rw [message_subPolynomial, message_pairPolynomial]

def cubicPhase {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R)
    (u : Matrix P (Fin m) R) (secret : Fin n → R) : R :=
  ∑ pair, 4 * secret (first pair) * secret (second pair) *
    tailPhase (first pair) (second pair) (projectedMask a u pair) secret

def sourceError {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (u : Matrix P (Fin m) R)
    (secret : Fin n → R) (error : Fin m → R) : R :=
  ∑ pair, character (secret (first pair)) * character (secret (second pair)) *
    dotProduct (u pair) error

/-- Actual original-key phase, with no unproved cancellation/noise premise. -/
theorem phase_real {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (a : Matrix (Fin n) (Fin m) R) (u : Matrix P (Fin m) R)
    (secret : Fin n → R) (hsecret : ∀ row, secret row * secret row = secret row)
    (error : Fin m → R) :
    RecursiveQuadratic.decrypt secret (compile first second a u (vecMul secret a + error)) =
      cubicPhase first second a u secret + sourceError first second u secret error := by
  rw [decrypt_compile]
  unfold cubicPhase sourceError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  have hprojection : dotProduct (u pair) (vecMul secret a + error) =
      dotProduct (projectedMask a u pair) secret + dotProduct (u pair) error := by
    rw [dotProduct_add, dotProduct_comm (u pair) (vecMul secret a), ← dotProduct_mulVec]
    rw [dotProduct_comm]
    rfl
  rw [hprojection, mul_add]
  have h := character_lower_identity (first pair) (second pair) (hpair pair)
    (projectedMask a u pair) secret (hsecret _) (hsecret _)
  linear_combination h

theorem character_product_magnitude {q n : ℕ} [NeZero q] (bits : Fin n → Bool)
    (i j : Fin n) (value : ZMod q) :
    (LatticeCrypto.centeredRepr (character (GSWSelfKey.binaryEmbed bits i) *
      character (GSWSelfKey.binaryEmbed bits j) * value)).natAbs =
      (LatticeCrypto.centeredRepr value).natAbs := by
  cases hi : bits i <;> cases hj : bits j <;>
    norm_num [character, GSWSelfKey.binaryEmbed, hi, hj, LatticeCrypto.centeredRepr_natAbs_neg]

/-- The bound uses actual source errors and public coefficient norms only. -/
theorem sourceError_bound {q n m : ℕ} [NeZero q] {P : Type} [Fintype P]
    (first second : P → Fin n) (u : Matrix P (Fin m) (ZMod q))
    (bits : Fin n → Bool) (error : Fin m → ZMod q) (E : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ E) :
    (LatticeCrypto.centeredRepr (sourceError first second u (GSWSelfKey.binaryEmbed bits) error)).natAbs ≤
      (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (u pair column)).natAbs) * E := by
  classical
  letI : DecidableEq P := Classical.typeDecidableEq P
  unfold sourceError
  calc
    _ ≤ ∑ pair, (LatticeCrypto.centeredRepr (character (GSWSelfKey.binaryEmbed bits (first pair)) *
        character (GSWSelfKey.binaryEmbed bits (second pair)) * dotProduct (u pair) error)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le (q := q) (Index := P)
        (fun pair ↦ character (GSWSelfKey.binaryEmbed bits (first pair)) *
          character (GSWSelfKey.binaryEmbed bits (second pair)) * dotProduct (u pair) error) Finset.univ
    _ = ∑ pair, (LatticeCrypto.centeredRepr (dotProduct (u pair) error)).natAbs := by
      apply Finset.sum_congr rfl
      intro pair _
      exact character_product_magnitude bits _ _ _
    _ ≤ ∑ pair, (∑ column, (LatticeCrypto.centeredRepr (u pair column)).natAbs) * E := by
      apply Finset.sum_le_sum
      intro pair _
      exact GSWQuadraticPreimageRowSupport.projection_noise_bound _ _ _ _ (le_refl _) herror
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Publicly combine transpose entries and absorb the diagonal into the linear
coordinate. This is the upper-triangular representation used by replay. -/
def normalize {R : Type} [CommRing R] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) : RecursiveQuadratic.Ciphertext R n :=
  (fun row column ↦ if row < column then ciphertext.1 row column + ciphertext.1 column row else 0,
   fun row ↦ ciphertext.2.1 row - ciphertext.1 row row, ciphertext.2.2)

theorem normalize_decrypt {R : Type} [CommRing R] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) (secret : Fin n → R)
    (hsecret : ∀ row, secret row * secret row = secret row) :
    RecursiveQuadratic.decrypt secret (normalize ciphertext) = RecursiveQuadratic.decrypt secret ciphertext := by
  let diagonalValues := fun row ↦ ciphertext.1 row row
  let upper : Matrix (Fin n) (Fin n) R := fun row column ↦
    if row < column then ciphertext.1 column row else 0
  have hmatrix : (normalize ciphertext).1 =
      ciphertext.1 + upper - upper.transpose - Matrix.diagonal diagonalValues := by
    ext row column
    rcases lt_trichotomy row column with h | h | h
    · have hn := ne_of_lt h
      have hreverse := not_lt_of_ge (le_of_lt h)
      simp [normalize, upper, h, hn, hreverse]
    · subst column
      simp [normalize, upper, diagonalValues]
    · have hn := ne_of_gt h
      have hreverse := not_lt_of_ge (le_of_lt h)
      simp [normalize, upper, h, hn, hreverse]
  have hdiag : dotProduct secret ((Matrix.diagonal diagonalValues).mulVec secret) =
      dotProduct diagonalValues secret := by
    simp only [dotProduct, mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro row _
    calc
      _ = diagonalValues row * (secret row * secret row) := by ring
      _ = _ := by rw [hsecret]
  have hquad : dotProduct (vecMul secret (normalize ciphertext).1) secret =
      dotProduct (vecMul secret ciphertext.1) secret - dotProduct diagonalValues secret := by
    calc
      _ = dotProduct secret ((normalize ciphertext).1.mulVec secret) :=
        (dotProduct_mulVec secret _ secret).symm
      _ = dotProduct secret (ciphertext.1.mulVec secret) - dotProduct diagonalValues secret := by
        rw [hmatrix, sub_mulVec, sub_mulVec, add_mulVec, dotProduct_sub,
          dotProduct_sub, dotProduct_add, dotProduct_transpose_mulVec, hdiag]
        ring
      _ = _ := by rw [dotProduct_mulVec]
  unfold RecursiveQuadratic.decrypt
  rw [hquad]
  change ciphertext.2.2 + dotProduct (ciphertext.2.1 - diagonalValues) secret - _ = _
  rw [sub_dotProduct]
  ring

def compileCanonical {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (a : Matrix (Fin n) (Fin m) R)
    (u : Matrix P (Fin m) R) (bodies : Fin m → R) : RecursiveQuadratic.Ciphertext R n :=
  normalize (compile first second a u bodies)

theorem phase_canonical {R P : Type} [CommRing R] [Fintype P] {n m : ℕ}
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (a : Matrix (Fin n) (Fin m) R) (u : Matrix P (Fin m) R)
    (secret : Fin n → R) (hsecret : ∀ row, secret row * secret row = secret row)
    (error : Fin m → R) :
    RecursiveQuadratic.decrypt secret (compileCanonical first second a u (vecMul secret a + error)) =
      cubicPhase first second a u secret + sourceError first second u secret error := by
  rw [compileCanonical, normalize_decrypt _ secret hsecret]
  exact phase_real first second hpair a u secret hsecret error

theorem phase_error_bound {q n m : ℕ} [NeZero q] {P : Type} [Fintype P]
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (a : Matrix (Fin n) (Fin m) (ZMod q)) (u : Matrix P (Fin m) (ZMod q))
    (bits : Fin n → Bool) (error : Fin m → ZMod q) (E : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ E) :
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
        (compileCanonical first second a u (vecMul (GSWSelfKey.binaryEmbed bits) a + error)) -
        cubicPhase first second a u (GSWSelfKey.binaryEmbed bits))).natAbs ≤
      (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (u pair column)).natAbs) * E := by
  have hsecret : ∀ row, GSWSelfKey.binaryEmbed (R := ZMod q) bits row *
      GSWSelfKey.binaryEmbed bits row = GSWSelfKey.binaryEmbed bits row := by
    intro row
    cases hb : bits row <;> simp [GSWSelfKey.binaryEmbed, hb]
  rw [phase_canonical first second hpair a u _ hsecret, add_sub_cancel_left]
  exact sourceError_bound first second u bits error E herror

def addZero {R : Type} [CommRing R] {n : ℕ}
    (zero ciphertext : RecursiveQuadratic.Ciphertext R n) : RecursiveQuadratic.Ciphertext R n :=
  (zero.1 + ciphertext.1, zero.2.1 + ciphertext.2.1, zero.2.2 + ciphertext.2.2)

theorem decrypt_addZero {R : Type} [CommRing R] {n : ℕ}
    (zero ciphertext : RecursiveQuadratic.Ciphertext R n) (secret : Fin n → R) :
    RecursiveQuadratic.decrypt secret (addZero zero ciphertext) =
      RecursiveQuadratic.decrypt secret zero + RecursiveQuadratic.decrypt secret ciphertext := by
  simp only [RecursiveQuadratic.decrypt, addZero, vecMul_add, add_dotProduct]
  ring

theorem phase_error_bound_with_zero {q n m : ℕ} [NeZero q] {P : Type} [Fintype P]
    (first second : P → Fin n) (hpair : ∀ pair, first pair ≠ second pair)
    (a : Matrix (Fin n) (Fin m) (ZMod q)) (u : Matrix P (Fin m) (ZMod q))
    (bits : Fin n → Bool) (error : Fin m → ZMod q) (E E0 : ℕ)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ E)
    (zero : RecursiveQuadratic.Ciphertext (ZMod q) n)
    (hzero : (LatticeCrypto.centeredRepr (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits) zero)).natAbs ≤ E0) :
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits)
        (addZero zero (compileCanonical first second a u (vecMul (GSWSelfKey.binaryEmbed bits) a + error))) -
        cubicPhase first second a u (GSWSelfKey.binaryEmbed bits))).natAbs ≤
      E0 + (∑ pair, ∑ column, (LatticeCrypto.centeredRepr (u pair column)).natAbs) * E := by
  rw [decrypt_addZero, add_sub_assoc]
  exact (TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _).trans
    (Nat.add_le_add hzero (phase_error_bound first second hpair a u bits error E herror))

def first3 : Fin 3 → Fin 3 := ![0, 0, 1]
def second3 : Fin 3 → Fin 3 := ![1, 2, 2]

theorem first3_ne_second3 (pair : Fin 3) : first3 pair ≠ second3 pair := by
  fin_cases pair <;> decide

def coefficient3 {R : Type} [CommRing R] {m : ℕ}
    (a : Matrix (Fin 3) (Fin m) R) (u : Matrix (Fin 3) (Fin m) R) : R :=
  projectedMask a u 0 2 + projectedMask a u 1 1 + projectedMask a u 2 0

/-- Exact modular-preimage certificate for the three-bit case, without dividing
by four in the ring. The experiment solves C*u=w/4 over modulus q/4 instead. -/
theorem cubicPhase_three {R : Type} [CommRing R] {m : ℕ}
    (a : Matrix (Fin 3) (Fin m) R) (u : Matrix (Fin 3) (Fin m) R) (secret : Fin 3 → R) :
    cubicPhase first3 second3 a u secret = 4 * coefficient3 a u * secret 0 * secret 1 * secret 2 := by
  simp [cubicPhase, tailPhase, first3, second3, coefficient3, Fin.sum_univ_succ]
  ring

end FormalProof4FHE.LWE.GSWLinearCharacterCompiler
