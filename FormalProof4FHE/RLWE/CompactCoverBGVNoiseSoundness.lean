/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverBGVExactNoise
import FormalProof4FHE.RLWE.CenteredBinomial

/-!
# Soundness lemmas for the scalar compact-cover BGV noise recurrence

These lemmas justify the algebraic forms used by the exact-natural recurrence:
coefficientwise addition and scaling, degree-N signed convolution, sums of
gadget rows, BGV multiplication, and modulus-drop rounding.
-/

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVNoiseSoundness

open BigOperators CompactCoverBGVExactNoise

abbrev Coefficients (count : ℕ) := Fin count → ℤ

def CoefficientBound {count : ℕ} (value : Coefficients count) (bound : ℕ) : Prop :=
  ∀ index, (value index).natAbs ≤ bound

def cbdCoefficients {count eta : ℕ}
    (coins : FormalProof4FHE.RLWE.CenteredBinomial.CoinTable count eta) :
    Coefficients count :=
  fun index => FormalProof4FHE.RLWE.CenteredBinomial.signedWeight (coins index)

theorem cbdCoefficients_bound {count eta : ℕ}
    (coins : FormalProof4FHE.RLWE.CenteredBinomial.CoinTable count eta) :
    CoefficientBound (cbdCoefficients coins) eta := by
  intro index
  have bound := FormalProof4FHE.RLWE.CenteredBinomial.abs_signedWeight_le
    (coins index)
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  exact bound

theorem coefficientBound_zero (count bound : ℕ) :
    CoefficientBound (fun _ : Fin count => 0) bound := by
  intro index
  simp

theorem coefficientBound_add {count leftBound rightBound : ℕ}
    {left right : Coefficients count}
    (hleft : CoefficientBound left leftBound)
    (hright : CoefficientBound right rightBound) :
    CoefficientBound (fun index => left index + right index)
      (leftBound + rightBound) := by
  intro index
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hleft index) (hright index))

theorem coefficientBound_scale {count bound : ℕ}
    (scalar : ℤ) {value : Coefficients count}
    (hvalue : CoefficientBound value bound) :
    CoefficientBound (fun index => scalar * value index) (scalar.natAbs * bound) := by
  intro index
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul_left scalar.natAbs (hvalue index)

/-- A signed cyclic/negacyclic convolution.  Only the absolute-one property of
the signs matters to the infinity-norm proof. -/
def signedConvolution {count : ℕ}
    (sign : Fin count → Fin count → ℤ)
    (permutation : Fin count → Fin count → Fin count)
    (left right : Coefficients count) : Coefficients count :=
  fun output => ∑ input : Fin count,
    sign output input * left input * right (permutation output input)

theorem signedConvolution_bound {count leftBound rightBound : ℕ}
    (sign : Fin count → Fin count → ℤ)
    (permutation : Fin count → Fin count → Fin count)
    (hsign : ∀ output input, (sign output input).natAbs ≤ 1)
    {left right : Coefficients count}
    (hleft : CoefficientBound left leftBound)
    (hright : CoefficientBound right rightBound) :
    CoefficientBound (signedConvolution sign permutation left right)
      (count * leftBound * rightBound) := by
  intro output
  unfold signedConvolution
  calc
    _ ≤ ∑ input : Fin count,
        (sign output input * left input *
          right (permutation output input)).natAbs :=
      Int.natAbs_sum_le Finset.univ _
    _ ≤ ∑ _input : Fin count, leftBound * rightBound := by
      apply Finset.sum_le_sum
      intro input _
      simp only [Int.natAbs_mul]
      calc
        (sign output input).natAbs * (left input).natAbs *
            (right (permutation output input)).natAbs
            ≤ 1 * leftBound * rightBound := by
              gcongr
              · exact hsign output input
              · exact hleft input
              · exact hright _
        _ = leftBound * rightBound := by simp
    _ = count * leftBound * rightBound := by simp [mul_assoc]

theorem coefficientBound_sum {rows count bound : ℕ}
    {values : Fin rows → Coefficients count}
    (hvalues : ∀ row, CoefficientBound (values row) bound) :
    CoefficientBound (fun index => ∑ row, values row index) (rows * bound) := by
  intro index
  calc
    _ ≤ ∑ row : Fin rows, (values row index).natAbs :=
      Int.natAbs_sum_le Finset.univ _
    _ ≤ ∑ _row : Fin rows, bound := by
      exact Finset.sum_le_sum fun row _ => hvalues row index
    _ = rows * bound := by simp

/-- The exact worst-case gadget-switch factor used by `keySwitchError`: each
of `rows` digit/error convolutions costs at most `degree*digitBound*errorBound`. -/
theorem gadgetKeySwitch_bound {rows count digitBound errorBound : ℕ}
    (sign : Fin count → Fin count → ℤ)
    (permutation : Fin count → Fin count → Fin count)
    (hsign : ∀ output input, (sign output input).natAbs ≤ 1)
    (digits errors : Fin rows → Coefficients count)
    (hdigits : ∀ row, CoefficientBound (digits row) digitBound)
    (herrors : ∀ row, CoefficientBound (errors row) errorBound) :
    CoefficientBound
      (fun index => ∑ row,
        signedConvolution sign permutation (digits row) (errors row) index)
      (rows * count * digitBound * errorBound) := by
  have each (row : Fin rows) :
      CoefficientBound (signedConvolution sign permutation (digits row) (errors row))
        (count * digitBound * errorBound) :=
    signedConvolution_bound sign permutation hsign (hdigits row) (herrors row)
  have total := coefficientBound_sum each
  simpa only [mul_assoc] using total

/-- Exact BGV multiplication phase before relinearization or modulus drop. -/
theorem multiplication_phase {R : Type} [CommRing R]
    (plaintextModulus leftMessage rightMessage leftError rightError : R) :
    (leftMessage + plaintextModulus * leftError) *
        (rightMessage + plaintextModulus * rightError) =
      leftMessage * rightMessage + plaintextModulus *
        (leftMessage * rightError + rightMessage * leftError +
          plaintextModulus * leftError * rightError) := by
  ring

/-- Integer magnitude bound corresponding to the multiplication term in the
executable recurrence. -/
theorem multiplication_error_bound
    (plaintextModulus messageBound leftBound rightBound : ℕ)
    (leftMessage rightMessage leftError rightError : ℤ)
    (hlm : leftMessage.natAbs ≤ messageBound)
    (hrm : rightMessage.natAbs ≤ messageBound)
    (hle : leftError.natAbs ≤ leftBound)
    (hre : rightError.natAbs ≤ rightBound) :
    (leftMessage * rightError + rightMessage * leftError +
      plaintextModulus * leftError * rightError).natAbs ≤
        messageBound * (leftBound + rightBound) +
          plaintextModulus * leftBound * rightBound := by
  calc
    _ ≤ (leftMessage * rightError).natAbs +
        (rightMessage * leftError).natAbs +
        (plaintextModulus * leftError * rightError).natAbs := by
      omega
    _ ≤ messageBound * rightBound + messageBound * leftBound +
        plaintextModulus * leftBound * rightBound := by
      simp only [Int.natAbs_mul]
      norm_num
      gcongr
    _ = messageBound * (leftBound + rightBound) +
        plaintextModulus * leftBound * rightBound := by ring

/-- One modulus-drop quotient error plus the aggregate signed rounding error. -/
theorem modulusDrop_error_bound (quotient rounding : ℤ)
    (quotientBound roundingBound : ℕ)
    (hquotient : quotient.natAbs ≤ quotientBound)
    (hrounding : rounding.natAbs ≤ roundingBound) :
    (quotient + rounding).natAbs ≤ quotientBound + roundingBound :=
  (Int.natAbs_add_le _ _).trans (Nat.add_le_add hquotient hrounding)

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVNoiseSoundness
