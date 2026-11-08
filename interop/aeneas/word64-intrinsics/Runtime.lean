import Aeneas.Std

/-! Closed 64-bit bit-count semantics. A zero nonzero-ctlz operand is undefined,
not a successful count. Population count is total and its u32 conversion is exact.
These definitions give no physical attacker-work charge or compiler theorem. -/
namespace HasteBootsWord64Intrinsics
open Aeneas Aeneas.Std

def leading (word : U64) : Result U32 :=
  if word.val = 0 then .fail .undef
  else .ok (core.num.U64.leading_zeros word)

def population (word : U64) : U32 :=
  ⟨BitVec.ofNat 32 word.bv.cpop.toNat⟩

theorem leading_zero (word : U64) (zero : word.val = 0) : leading word = .fail .undef := by
  simp only [leading, zero, ite_true]

theorem leading_nonzero (word : U64) (positive : word.val ≠ 0) :
    leading word = .ok (core.num.U64.leading_zeros word) := by
  simp only [leading, positive, ite_false]

theorem leading_bits (word : U64) (positive : word.val ≠ 0) : word.bv ≠ 0 := by
  intro same
  apply positive
  exact (congrArg BitVec.toNat same).trans BitVec.toNat_zero

theorem leading_value (word : U64) (positive : word.val ≠ 0) :
    (core.num.U64.leading_zeros word).val = 64 - Nat.log 2 word.val - 1 := by
  have fits : 64 - Nat.log 2 word.val - 1 < 2^32 := by omega
  simp only [core.num.U64.leading_zeros, UScalar.val,
    BitVec.leadingZeros, leading_bits word positive, ite_false]
  exact Nat.mod_eq_of_lt fits

theorem leading_bound (word : U64) (positive : word.val ≠ 0) :
    (core.num.U64.leading_zeros word).val ≤ 63 := by
  rw [leading_value word positive]
  omega

theorem population_value (word : U64) :
    (population word).val = word.bv.cpop.toNat := by
  have bound : word.bv.cpop.toNat ≤ 64 := BitVec.toNat_cpop_le word.bv
  have fits : word.bv.cpop.toNat < 2^32 := by omega
  exact Nat.mod_eq_of_lt fits

theorem population_bit_sum (word : U64) :
    (population word).val = (Finset.range 64).sum (fun i => (word.bv.getLsbD i).toNat) := by
  have sum (n acc : Nat) : word.bv.cpopNatRec n acc =
      acc + (Finset.range n).sum (fun i => (word.bv.getLsbD i).toNat) := by
    induction n generalizing acc with
    | zero => simp [BitVec.cpopNatRec]
    | succ n ih =>
      rw [BitVec.cpopNatRec, ih, Finset.sum_range_succ]
      omega
  rw [population_value, BitVec.toNat_cpop]
  simpa only [Nat.zero_add] using sum 64 0

theorem population_bound (word : U64) : (population word).val ≤ 64 := by
  rw [population_value]
  exact BitVec.toNat_cpop_le word.bv

theorem population_zero : population 0#u64 = 0#u32 := rfl

theorem population_full : population 18446744073709551615#u64 = 64#u32 := rfl

theorem population_high : population 9223372036854775808#u64 = 1#u32 := rfl

end HasteBootsWord64Intrinsics
