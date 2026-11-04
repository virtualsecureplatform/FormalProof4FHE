module

public import FormalProof4FHE.HasteBoots.NativeGoldLaneWeights
import all Init.Data.Nat.Power2.Basic

@[expose] public section

/-!
# Native scalar-query outer shape checks

The nonzero power-of-two bit test, ilog2, checked usize dimension addition
and exact original point length are retained. The power and machine shift
bounds are derived from these checks, without a supplied geometry decoder
or an additional work cap. Instruction refinement remains separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarQueryShape

def powerOfTwo (width : ℕ) : Bool := decide (width ≠ 0) && decide (width &&& (width - 1) = 0)
def laneBits (width : ℕ) : ℕ := width.log2

def dimension (sourceVars width pointLength : ℕ) : Bool :=
  decide (sourceVars + laneBits width < 2 ^ 64) && decide (sourceVars + laneBits width = pointLength)

def check (sourceVars width pointLength : ℕ) : Bool :=
  NativeGoldProjection.dimensions width && powerOfTwo width && dimension sourceVars width pointLength

theorem powerOfTwo_iff (width : ℕ) : powerOfTwo width = true ↔ width.isPowerOfTwo := by
  rw [powerOfTwo, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo]

theorem power_eq_laneBits (width : ℕ) (power : powerOfTwo width = true) : width = 2 ^ laneBits width := by
  have existsPower := (powerOfTwo_iff width).mp power
  change ∃ exponent, width = 2 ^ exponent at existsPower
  obtain ⟨exponent, rfl⟩ := existsPower
  rw [laneBits, Nat.log2_two_pow]

theorem dimension_iff (sourceVars width pointLength : ℕ) : dimension sourceVars width pointLength = true ↔
    sourceVars + laneBits width < 2 ^ 64 ∧ sourceVars + laneBits width = pointLength := by
  simp only [dimension, Bool.and_eq_true, decide_eq_true_eq]

theorem check_iff (sourceVars width pointLength : ℕ) : check sourceVars width pointLength = true ↔
    NativeGoldProjection.dimensions width = true ∧ powerOfTwo width = true ∧
      sourceVars + laneBits width < 2 ^ 64 ∧ sourceVars + laneBits width = pointLength := by
  simp only [check, Bool.and_eq_true, dimension_iff, and_assoc]

theorem checked_dimensions (sourceVars width pointLength : ℕ) (accepted : check sourceVars width pointLength = true) :
    NativeGoldProjection.dimensions width = true := (check_iff _ _ _).mp accepted |>.1

theorem checked_power (sourceVars width pointLength : ℕ) (accepted : check sourceVars width pointLength = true) :
    width = 2 ^ laneBits width := power_eq_laneBits width ((check_iff _ _ _).mp accepted |>.2.1)

theorem checked_shift (sourceVars width pointLength : ℕ) (accepted : check sourceVars width pointLength = true) :
    laneBits width < 64 := NativeGoldLaneWeights.lane_bits_fits (checked_dimensions _ _ _ accepted)
      (checked_power _ _ _ accepted)

theorem checked_length (sourceVars width pointLength : ℕ) (accepted : check sourceVars width pointLength = true) :
    laneBits width + sourceVars = pointLength := by
  have length := (check_iff _ _ _).mp accepted |>.2.2.2
  omega

theorem checked_point_fits (sourceVars width pointLength : ℕ) (accepted : check sourceVars width pointLength = true) :
    pointLength < 2 ^ 64 := by
  have shape := (check_iff _ _ _).mp accepted
  omega

end FormalProof4FHE.HasteBoots.NativeScalarQueryShape
