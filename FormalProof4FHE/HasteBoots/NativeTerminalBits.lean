module

public import FormalProof4FHE.HasteBoots.NativePrefixMask
public import FormalProof4FHE.HasteBoots.NativeUsizeMessage
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# Native threshold bits and low-bit-first lookup addresses

The machine threshold is a 64-bit usize. The shift-and-mask predicate is
connected to the exact coordinate of the existing Boolean address bijection;
no bit-decoding certificate is supplied by the caller.
-/

namespace FormalProof4FHE.HasteBoots.NativeTerminalBits

open NativeUsizeMessage (Usize)

/-- Natural interpretation of the unsigned native shift-and-mask expression. -/
def bit (count : Usize) (index : ℕ) : Bool := decide ((count.val >>> index) &&& 1 = 1)

theorem address_bit {n : ℕ} (cell : PackedZeroEquality.Cell (n + 1)) :
    (NativeEqualityTable.address (n + 1) cell).val =
      Nat.bit (finTwoEquiv (cell 0)) (NativeEqualityTable.address n (fun i => cell i.succ)).val := by
  change (FlatMatrixFold.index (n + 1)
    (finTwoEquiv (cell 0), (PackedEqualityCube.bits n).symm (fun i => cell i.succ))).val = _
  rw [FlatMatrixFold.index_succ_val]
  generalize finTwoEquiv (cell 0) = selected
  cases selected <;> rfl

theorem address_testBit (n : ℕ) (cell : PackedZeroEquality.Cell n) (index : Fin n) :
    Nat.testBit (NativeEqualityTable.address n cell).val index.val = finTwoEquiv (cell index) := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) index
    · simp only [Fin.val_zero]
      rw [address_bit, Nat.testBit_bit_zero]
    · simp only [Fin.val_succ]
      rw [address_bit, Nat.testBit_bit_succ, ih]

theorem bit_testBit (count : Usize) (index : ℕ) : bit count index = Nat.testBit count.val index := by
  apply Bool.eq_iff_iff.mpr
  simp only [bit, decide_eq_true_eq, Nat.testBit, bne_iff_ne]
  rw [Nat.land_comm _ 1, Nat.one_and_eq_mod_two]
  have bound := Nat.mod_lt (count.val >>> index) (by decide : 0 < 2)
  omega

/-- Every tested native bit is exactly the corresponding threshold coordinate. -/
theorem threshold_bit (n : ℕ) (count : Usize) (inside : count.val < 2 ^ n) (index : Fin n) :
    bit count index.val = finTwoEquiv ((NativeEqualityTable.address n).symm ⟨count.val, inside⟩ index) := by
  rw [bit_testBit]
  have decoded := address_testBit n ((NativeEqualityTable.address n).symm ⟨count.val, inside⟩) index
  simpa only [Equiv.apply_symm_apply] using decoded

end FormalProof4FHE.HasteBoots.NativeTerminalBits
