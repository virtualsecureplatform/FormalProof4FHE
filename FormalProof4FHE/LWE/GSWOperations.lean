/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWSelfKey

/-!
# GSW matrix phases and homomorphic error identities

Connect the fresh-sampling model to the rectangular GSW matrix presentation and prove the
exact addition and multiplication error identities.  Multiplication takes a gadget
decomposition with a checked reconstruction equation.  This equation alone does not prove
that the digits are short, that decoding succeeds, or that a refresh is repeatable.
-/

open Matrix

namespace FormalProof4FHE.LWE.GSWOperations

/-- The body-first decryption vector for the sign convention in `GSWSelfKey`. -/
def extendedSecret {R : Type} [Ring R] {dimension : ℕ} (secret : Fin dimension → R) :
    Fin (dimension + 1) → R :=
  Fin.cases 1 (fun row ↦ -secret row)

/-- Assemble the body and mask rows into the rectangular ciphertext matrix. -/
def ciphertextMatrix {R : Type} {dimension samples : ℕ}
    (transcript : BatchTranscript R dimension samples) :
    Matrix (Fin (dimension + 1)) (Fin samples) R :=
  fun row column ↦ Fin.cases (transcript.2 column)
    (fun maskRow ↦ transcript.1 maskRow column) row

/-- Matrix decryption is exactly body minus the LWE inner product. -/
theorem vecMul_ciphertextMatrix {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R) (transcript : BatchTranscript R dimension samples) :
    vecMul (extendedSecret secret) (ciphertextMatrix transcript) =
      transcript.2 - vecMul secret transcript.1 := by
  funext column
  simp [vecMul, dotProduct, extendedSecret, ciphertextMatrix, Fin.sum_univ_succ,
    sub_eq_add_neg]

/-- The full gadget matrix for a public layout. -/
def gadgetMatrix {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : GSWSelfKey.Layout R dimension samples) :
    Matrix (Fin (dimension + 1)) (Fin samples) R :=
  ciphertextMatrix (GSWSelfKey.maskShift layout (fun _ ↦ 1),
    GSWSelfKey.bodyShift layout (fun _ ↦ 1))

theorem vecMul_gadgetMatrix {R : Type} [Ring R] {dimension samples : ℕ}
    (layout : GSWSelfKey.Layout R dimension samples) (secret : Fin dimension → R) :
    vecMul (extendedSecret secret) (gadgetMatrix layout) =
      GSWSelfKey.phaseMessage layout secret (fun _ ↦ 1) := by
  rw [gadgetMatrix, vecMul_ciphertextMatrix, GSWSelfKey.vecMul_maskShift]
  abel

/-- Algebraic ciphertext error relative to its claimed plaintext and the gadget matrix. -/
def noise {R : Type} [CommRing R] {rows columns : ℕ}
    (secret : Fin rows → R) (gadget ciphertext : Matrix (Fin rows) (Fin columns) R)
    (message : R) : Fin columns → R :=
  vecMul secret ciphertext - message • vecMul secret gadget

/-- Fresh encryption in the sampler model has exactly its sampled error, in matrix form. -/
theorem fresh_noise {R : Type} [CommRing R] {dimension samples : ℕ}
    (layout : GSWSelfKey.Layout R dimension samples) (secret : Fin dimension → R)
    (message : R) (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) :
    noise (extendedSecret secret) (gadgetMatrix layout)
      (ciphertextMatrix (GSWSelfKey.freshTranscript layout secret (fun _ ↦ message)
        challenge error)) message = error := by
  have hphase : GSWSelfKey.phaseMessage layout secret (fun _ ↦ message) =
      message • GSWSelfKey.phaseMessage layout secret (fun _ ↦ 1) := by
    funext column
    cases hcoordinate : layout.coordinate column with
    | none =>
      simp [GSWSelfKey.phaseMessage, hcoordinate, Pi.smul_apply, smul_eq_mul]
    | some row =>
      simp [GSWSelfKey.phaseMessage, hcoordinate, Pi.smul_apply, smul_eq_mul]
      ring
  rw [noise, vecMul_ciphertextMatrix, GSWSelfKey.freshTranscript_phase,
    vecMul_gadgetMatrix, hphase]
  abel

/-- Addition adds both plaintexts and their exact error vectors. -/
theorem noise_add {R : Type} [CommRing R] {rows columns : ℕ}
    (secret : Fin rows → R) (gadget first second : Matrix (Fin rows) (Fin columns) R)
    (firstMessage secondMessage : R) :
    noise secret gadget (first + second) (firstMessage + secondMessage) =
      noise secret gadget first firstMessage + noise secret gadget second secondMessage := by
  simp only [noise, vecMul_add, add_smul]
  abel

/-- GSW multiplication has error `e1 * digits + mu1 * e2`, with no secret-key change.
The reconstruction hypothesis must later be supplied by the actual gadget decomposition. -/
theorem noise_mul {R : Type} [CommRing R] {rows columns : ℕ}
    (secret : Fin rows → R) (gadget first second : Matrix (Fin rows) (Fin columns) R)
    (digits : Matrix (Fin columns) (Fin columns) R)
    (firstMessage secondMessage : R) (hreconstruct : gadget * digits = second) :
    noise secret gadget (first * digits) (firstMessage * secondMessage) =
      vecMul (noise secret gadget first firstMessage) digits +
        firstMessage • noise secret gadget second secondMessage := by
  simp only [noise, sub_vecMul, smul_vecMul, vecMul_vecMul, hreconstruct, smul_sub,
    mul_smul]
  abel

end FormalProof4FHE.LWE.GSWOperations
