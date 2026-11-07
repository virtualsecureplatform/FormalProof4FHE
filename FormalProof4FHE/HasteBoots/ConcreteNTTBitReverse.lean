module
public import FormalProof4FHE.HasteBoots.ConcreteNTTPlanRootPowers
public import Mathlib.Data.BitVec
@[expose] public section

/-! The locked backend bit_rev on the 64-bit usize path: reverse all 64 bits,
then shift right by 64-nbits. The bounded permutation is derived from this
word expression, not supplied as an index callback. Actual Rust instruction and
usize-width refinement, and the native positive-width shift domain, remain
separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTBitReverse

def word (bits index : ℕ) : ℕ :=
  ((BitVec.ofNat 64 index).reverse >>> (64-bits)).toNat

def narrow (bits index : ℕ) : ℕ := (BitVec.ofNat bits index).reverse.toNat

theorem word_eq_narrow (bits index : ℕ) (width : bits ≤ 64) : word bits index = narrow bits index := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (((BitVec.ofNat 64 index).reverse >>> (64-bits)).getLsbD j) =
    ((BitVec.ofNat bits index).reverse.getLsbD j)
  rw [BitVec.getLsbD_ushiftRight,BitVec.getLsbD_reverse,BitVec.getLsbD_reverse,
    BitVec.getMsbD_eq_getLsbD,BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_ofNat,BitVec.getLsbD_ofNat]
  by_cases inside : j < bits
  · have full : 64-bits+j < 64 := by omega
    have small : bits-1-j < bits := by omega
    have fullIndex : bits-1-j < 64 := by omega
    have same : 64-1-(64-bits+j) = bits-1-j := by omega
    simp only [inside,full,small,same,fullIndex,decide_true,Bool.true_and]
  · have outside : ¬64-bits+j < 64 := by omega
    simp only [inside,outside,decide_false,Bool.false_and]

theorem shift_domain (bits : ℕ) (positive : 0 < bits) (width : bits ≤ 64) :
    64-bits < 64 ∧ bits+(64-bits) = 64 := by omega

theorem word_lt (bits index : ℕ) (width : bits ≤ 64) : word bits index < 2^bits := by
  rw [word_eq_narrow bits index width]
  exact (BitVec.ofNat bits index).reverse.isLt

theorem narrow_involutive (bits index : ℕ) (bound : index < 2^bits) :
    narrow bits (narrow bits index) = index := by
  simp only [narrow,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.reverse_reverse_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]

theorem word_involutive (bits index : ℕ) (width : bits ≤ 64) (bound : index < 2^bits) :
    word bits (word bits index) = index := by
  rw [word_eq_narrow bits _ width,word_eq_narrow bits index width]
  exact narrow_involutive bits index bound

theorem word_injective (bits left right : ℕ) (width : bits ≤ 64)
    (leftBound : left < 2^bits) (rightBound : right < 2^bits)
    (same : word bits left = word bits right) : left = right := by
  have again := congrArg (word bits) same
  simpa only [word_involutive bits left width leftBound,word_involutive bits right width rightBound] using again

theorem word_zero (bits : ℕ) (width : bits ≤ 64) : word bits 0 = 0 := by
  rw [word_eq_narrow bits 0 width]
  unfold narrow
  have zero : (0 : BitVec bits).reverse = 0 := BitVec.reverse_eq_zero_iff.mpr rfl
  rw [show BitVec.ofNat bits 0 = 0 from rfl,zero]
  rfl

end FormalProof4FHE.HasteBoots.ConcreteNTTBitReverse
