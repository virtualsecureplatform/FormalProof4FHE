/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverBGVExactNoise
import FormalProof4FHE.RLWE.CompactCoverBGVNoiseSoundness

/-!
# End-to-end scalar compact-cover BGV correctness

This module joins the phase algebra, concrete digit-removal identity, exact
integer recurrence, and normalized gate closure into one specification-level
bootstrap theorem. The ciphertext carrier is represented by its decryption
phase; refinement from the C++ mask/body/RNS layout remains a separate
implementation relation.
-/

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVScalarCorrectness

open CompactCoverBGVExactNoise

/-- A ciphertext phase encrypts `message` with invariant factor `t` and error
`error`. -/
def Encodes {R : Type} [CommRing R]
    (plaintextModulus phase message error : R) : Prop :=
  phase = message + plaintextModulus * error

theorem encodes_add {R : Type} [CommRing R]
    (t leftPhase rightPhase leftMessage rightMessage leftError rightError : R)
    (left : Encodes t leftPhase leftMessage leftError)
    (right : Encodes t rightPhase rightMessage rightError) :
    Encodes t (leftPhase + rightPhase) (leftMessage + rightMessage)
      (leftError + rightError) := by
  simp only [Encodes] at left right ⊢
  rw [left, right]
  ring

theorem encodes_scale {R : Type} [CommRing R]
    (t scalar phase message error : R)
    (encoded : Encodes t phase message error) :
    Encodes t (scalar * phase) (scalar * message) (scalar * error) := by
  simp only [Encodes] at encoded ⊢
  rw [encoded]
  ring

theorem encodes_multiply {R : Type} [CommRing R]
    (t leftPhase rightPhase leftMessage rightMessage leftError rightError : R)
    (left : Encodes t leftPhase leftMessage leftError)
    (right : Encodes t rightPhase rightMessage rightError) :
    Encodes t (leftPhase * rightPhase) (leftMessage * rightMessage)
      (leftMessage * rightError + rightMessage * leftError +
        t * leftError * rightError) := by
  simp only [Encodes] at left right ⊢
  rw [left, right]
  ring

/-- Exact division by `p` converts a `p²`-invariant removed phase into the
ordinary BGV `p` invariant without retaining the old low-level error. -/
theorem exactDivision_encodes {R : Type} [CommRing R]
    (p : Rˣ) (removedPhase message outputError : R)
    (removed : Encodes ((p : R) ^ 2) removedPhase
      ((p : R) * message) outputError) :
    Encodes (p : R) ((↑(p⁻¹) : R) * removedPhase) message outputError := by
  simp only [Encodes] at removed ⊢
  rw [removed]
  have inverse : (↑(p⁻¹) : R) * (p : R) = 1 := by simp
  calc
    (↑(p⁻¹) : R) * ((p : R) * message + (p : R) ^ 2 * outputError) =
        ((↑(p⁻¹) : R) * (p : R)) * message +
          (((↑(p⁻¹) : R) * (p : R)) * (p : R)) * outputError := by ring
    _ = message + (p : R) * outputError := by rw [inverse]; simp

/-- Complete phase theorem for the scalar bootstrap after trace and bounded
digit removal. -/
theorem scalarBootstrap_phase_correct {R : Type} [CommRing R]
    (p : Rˣ) (removedPhase outputPhase message outputError : R)
    (removed : Encodes ((p : R) ^ 2) removedPhase
      ((p : R) * message) outputError)
    (division : outputPhase = (↑(p⁻¹) : R) * removedPhase) :
    Encodes (p : R) outputPhase message outputError := by
  rw [division]
  exact exactDivision_encodes p removedPhase message outputError removed

/-- The concrete plaintext operation required by `removed` is not an
assumption: the checked degree-93 polynomial supplies it for every supported
carry and every message. -/
theorem concreteRemoval_plaintext
    (message : ZMod plaintextSquare) (carry : ℤ)
    (lower : -(digitErrorBound : ℤ) ≤ carry)
    (upper : carry ≤ digitErrorBound) :
    coefficientEval digitRemovalCoefficients
        ((plaintextPrime : ZMod plaintextSquare) * message + carry) =
      (plaintextPrime : ZMod plaintextSquare) * message :=
  digitRemovalPolynomial_correct message carry lower upper

/-- One theorem collecting the exact concrete obligations used by an
arbitrary-depth scalar FHE evaluation. -/
theorem concreteScalarCycle_correct
    (message : ZMod plaintextSquare) (carry : ℤ)
    (lower : -(digitErrorBound : ℤ) ≤ carry)
    (upper : carry ≤ digitErrorBound) :
    coefficientEval digitRemovalCoefficients
          ((plaintextPrime : ZMod plaintextSquare) * message + carry) =
        (plaintextPrime : ZMod plaintextSquare) * message ∧
      outputState.limbs = 13 ∧
      outputState.bound < outputCapacity ∧
      oneLimbAdditionState.bound ≤ acceptedInputError ∧
      multiplicationState.bound ≤ acceptedInputError := by
  exact ⟨concreteRemoval_plaintext message carry lower upper,
    selectedExactCycleCertificate.outputLevel,
    selectedExactCycleCertificate.outputFits,
    selectedExactCycleCertificate.additionCloses,
    selectedExactCycleCertificate.multiplicationCloses⟩

/-- The preceding concrete theorem composes indefinitely along every
normalized addition/multiplication circuit. -/
theorem concreteScalarFHE_refreshable {inputs : ℕ}
    (circuit : NormalizedScalarCircuit inputs) : circuit.Refreshable :=
  normalizedScalarCircuit_refreshable circuit

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVScalarCorrectness
