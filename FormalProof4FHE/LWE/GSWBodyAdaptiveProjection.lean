/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWOperations

/-!
# Public self-stable control factors

A factor P with GP=C and CP=C preserves the span of G,C and stabilizes
repeated right multiplication by one control. The exact error eigenrelation
depends on that control's bit. Distinct controls still have the ordinary
cross-error law; neither a useful shortness bound nor a secure reusable joint
family is asserted. The accompanying public-preimage experiment records
builder failures and complete multiple-control refresh trials.
-/

open Matrix

namespace FormalProof4FHE.LWE.GSWBodyAdaptiveProjection

variable {R : Type} [CommRing R] {rows width : ℕ}

def rightCMux (factor : Matrix (Fin width) (Fin width) R)
    (first second : Matrix (Fin rows) (Fin width) R) : Matrix (Fin rows) (Fin width) R :=
  second + (first - second) * factor

theorem span_action (gadget control : Matrix (Fin rows) (Fin width) R)
    (factor : Matrix (Fin width) (Fin width) R)
    (hbase : gadget * factor = control) (hstable : control * factor = control) (a b : R) :
    (a • gadget + b • control) * factor = (a + b) • control := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hbase, hstable, add_smul]

theorem rightCMux_span (gadget control : Matrix (Fin rows) (Fin width) R)
    (factor : Matrix (Fin width) (Fin width) R)
    (hbase : gadget * factor = control) (hstable : control * factor = control)
    (a b c d : R) :
    rightCMux factor (a • gadget + b • control) (c • gadget + d • control) =
      c • gadget + (a + b - c) • control := by
  rw [rightCMux, Matrix.sub_mul, span_action gadget control factor hbase hstable,
    span_action gadget control factor hbase hstable]
  ext row column
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- On a binary message, the control error is an exact zero/one eigenvector
of the public factor. This is a single-control relation, not a cross bound. -/
theorem control_error_eigen (secret : Fin rows → R)
    (gadget control : Matrix (Fin rows) (Fin width) R)
    (factor : Matrix (Fin width) (Fin width) R)
    (hbase : gadget * factor = control) (hstable : control * factor = control)
    (message : R) (hbit : message * message = message) :
    vecMul (GSWOperations.noise secret gadget control message) factor =
      (1 - message) • GSWOperations.noise secret gadget control message := by
  have hz : (1 - message) * message = 0 := by
    calc
      _ = message - message * message := by ring
      _ = 0 := by rw [hbit, sub_self]
  simp only [GSWOperations.noise, sub_vecMul, smul_vecMul, vecMul_vecMul, hbase, hstable]
  funext column
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = (1 - message) * vecMul secret control column := by ring
    _ = (1 - message) *
        (vecMul secret control column - message * vecMul secret gadget column) := by
      rw [mul_sub, ← mul_assoc, hz, zero_mul, sub_zero]

def iterateRight (gadget : Matrix (Fin rows) (Fin width) R)
    (factor : Matrix (Fin width) (Fin width) R) : ℕ → Matrix (Fin rows) (Fin width) R
  | 0 => gadget
  | steps + 1 => iterateRight gadget factor steps * factor

theorem iterateRight_positive (gadget control : Matrix (Fin rows) (Fin width) R)
    (factor : Matrix (Fin width) (Fin width) R)
    (hbase : gadget * factor = control) (hstable : control * factor = control) (steps : ℕ) :
    iterateRight gadget factor (steps + 1) = control := by
  induction steps with
  | zero => simpa [iterateRight] using hbase
  | succ steps ih =>
    change iterateRight gadget factor (steps + 1) * factor = control
    rw [ih, hstable]

/-- The unchanged error of one repeatedly used control does not imply a
bound for independent controls or a whole decryption/refresh computation. -/
theorem repeated_noise (secret : Fin rows → R)
    (gadget control : Matrix (Fin rows) (Fin width) R)
    (factor : Matrix (Fin width) (Fin width) R)
    (hbase : gadget * factor = control) (hstable : control * factor = control)
    (message : R) (steps : ℕ) :
    GSWOperations.noise secret gadget (iterateRight gadget factor (steps + 1)) message =
      GSWOperations.noise secret gadget control message := by
  rw [iterateRight_positive gadget control factor hbase hstable]

/-- Different controls retain the full cross-error law, without independence
or a cancellation/shortness premise. -/
theorem cross_error (secret : Fin rows → R)
    (gadget first second : Matrix (Fin rows) (Fin width) R)
    (factor : Matrix (Fin width) (Fin width) R) (hbase : gadget * factor = second)
    (firstMessage secondMessage : R) :
    GSWOperations.noise secret gadget (first * factor) (firstMessage * secondMessage) =
      vecMul (GSWOperations.noise secret gadget first firstMessage) factor +
        firstMessage • GSWOperations.noise secret gadget second secondMessage :=
  GSWOperations.noise_mul secret gadget first second factor firstMessage secondMessage hbase

/-- The public pairwise constraint is commutation on the gadget row space;
it does not assert that the full operators commute. -/
theorem gadget_commutator (gadget first second : Matrix (Fin rows) (Fin width) R)
    (firstFactor secondFactor : Matrix (Fin width) (Fin width) R)
    (hfirst : gadget * firstFactor = first) (hsecond : gadget * secondFactor = second) :
    gadget * (firstFactor * secondFactor - secondFactor * firstFactor) =
      first * secondFactor - second * firstFactor := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hfirst, hsecond]

/-- Pairwise public equality makes cross errors equal, but gives no bound
on their common value. -/
theorem cross_error_symmetry (secret : Fin rows → R)
    (gadget first second : Matrix (Fin rows) (Fin width) R)
    (firstFactor secondFactor : Matrix (Fin width) (Fin width) R)
    (hfirst : gadget * firstFactor = first) (hsecond : gadget * secondFactor = second)
    (hcross : first * secondFactor = second * firstFactor) (firstMessage secondMessage : R) :
    vecMul (GSWOperations.noise secret gadget first firstMessage) secondFactor +
        firstMessage • GSWOperations.noise secret gadget second secondMessage =
      vecMul (GSWOperations.noise secret gadget second secondMessage) firstFactor +
        secondMessage • GSWOperations.noise secret gadget first firstMessage := by
  calc
    _ = GSWOperations.noise secret gadget (first * secondFactor) (firstMessage * secondMessage) :=
      (cross_error secret gadget first second secondFactor hsecond firstMessage secondMessage).symm
    _ = GSWOperations.noise secret gadget (second * firstFactor) (secondMessage * firstMessage) := by
      rw [hcross, mul_comm firstMessage secondMessage]
    _ = _ := cross_error secret gadget second first firstFactor hfirst secondMessage firstMessage

end FormalProof4FHE.LWE.GSWBodyAdaptiveProjection
