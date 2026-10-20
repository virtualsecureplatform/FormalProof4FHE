/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWQuadraticPreimage
import FormalProof4FHE.LWE.RecursiveQuadratic

/-!
# Trying conversion with explicit auxiliary native quadratic ciphertexts

Public digits of the recursive quadratic matrix select native auxiliary
columns encoding weighted secret products. Conversion keeps the original
linear decryption secret and has an exact weighted auxiliary error sum.

These are conditional correctness identities. The joint ordinary-LWE security
of the auxiliary table is NOT asserted or introduced as an assumption. A
secure efficiently generated auxiliary table is the unresolved construction
obligation; merely supplying it would restate quadratic circular security.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWQuadraticAuxConversion

def convert {R I : Type} [CommRing R] [Fintype I] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) (coefficients : I → R)
    (auxiliary : I → BatchTranscript R n 1) : BatchTranscript R n 1 :=
  (fun row _ ↦ (-ciphertext.2.1 -
    ∑ index, coefficients index • (fun row ↦ (auxiliary index).1 row 0)) row,
   fun _ ↦ ciphertext.2.2 - ∑ index, coefficients index * (auxiliary index).2 0)

theorem phase_convert {R I : Type} [CommRing R] [Fintype I] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) (coefficients : I → R)
    (auxiliary : I → BatchTranscript R n 1) (secret : Fin n → R) :
    GSWQuadraticPreimage.phase secret (convert ciphertext coefficients auxiliary) 0 =
      ciphertext.2.2 + dotProduct ciphertext.2.1 secret -
        ∑ index, coefficients index * GSWQuadraticPreimage.phase secret (auxiliary index) 0 := by
  unfold GSWQuadraticPreimage.phase convert
  change (ciphertext.2.2 - ∑ index, coefficients index * (auxiliary index).2 0) -
    dotProduct secret (-ciphertext.2.1 -
      ∑ index, coefficients index • (fun row ↦ (auxiliary index).1 row 0)) = _
  rw [dotProduct_sub, dotProduct_neg, dotProduct_sum]
  simp_rw [dotProduct_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [dotProduct_comm secret ciphertext.2.1]
  ring

/-- A reconstructed quadratic term suffices for conversion of every actual
input ciphertext; the auxiliary error remains explicit. -/
theorem phase_convert_eq_decrypt_sub_error {R I : Type} [CommRing R] [Fintype I] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) (coefficients : I → R)
    (auxiliary : I → BatchTranscript R n 1) (secret : Fin n → R)
    (values errors : I → R)
    (hreconstruction : ∑ index, coefficients index * values index =
      dotProduct (vecMul secret ciphertext.1) secret)
    (hauxiliary : ∀ index,
      GSWQuadraticPreimage.phase secret (auxiliary index) 0 = values index + errors index) :
    GSWQuadraticPreimage.phase secret (convert ciphertext coefficients auxiliary) 0 =
      RecursiveQuadratic.decrypt secret ciphertext - ∑ index, coefficients index * errors index := by
  rw [phase_convert]
  simp_rw [hauxiliary, mul_add, Finset.sum_add_distrib]
  rw [hreconstruction]
  unfold RecursiveQuadratic.decrypt
  ring

/-- Public matrix reconstruction implies the phase reconstruction on every
key; it does not require a secret-dependent coefficient selection. -/
theorem quadratic_reconstruction {R I : Type} [CommRing R] [Fintype I] {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) R) (coefficients : I → R)
    (targets : I → Matrix (Fin n) (Fin n) R)
    (hreconstruction : matrix = ∑ index, coefficients index • targets index)
    (secret : Fin n → R) :
    ∑ index, coefficients index * dotProduct (vecMul secret (targets index)) secret =
      dotProduct (vecMul secret matrix) secret := by
  rw [hreconstruction]
  simp only [vecMul_sum, vecMul_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem phase_convert_of_matrix_reconstruction {R I : Type} [CommRing R] [Fintype I] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) (coefficients : I → R)
    (targets : I → Matrix (Fin n) (Fin n) R) (auxiliary : I → BatchTranscript R n 1)
    (hreconstruction : ciphertext.1 = ∑ index, coefficients index • targets index)
    (secret : Fin n → R) (errors : I → R)
    (hauxiliary : ∀ index, GSWQuadraticPreimage.phase secret (auxiliary index) 0 =
      dotProduct (vecMul secret (targets index)) secret + errors index) :
    GSWQuadraticPreimage.phase secret (convert ciphertext coefficients auxiliary) 0 =
      RecursiveQuadratic.decrypt secret ciphertext - ∑ index, coefficients index * errors index :=
  phase_convert_eq_decrypt_sub_error ciphertext coefficients auxiliary secret _ errors
    (quadratic_reconstruction ciphertext.1 coefficients targets hreconstruction secret) hauxiliary

end FormalProof4FHE.LWE.GSWQuadraticAuxConversion
