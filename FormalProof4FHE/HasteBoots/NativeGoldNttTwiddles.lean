module

public import FormalProof4FHE.HasteBoots.NativeGoldNtt

@[expose] public section

/-! The actual ordered twiddle writes compute canonical powers in bit-reversed
positions. No twiddle table or table-correctness certificate is supplied. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldNttTwiddles

open NativeFields NativeFieldRepresentation
open NativeGoldSolinas (Word)
open NativeGoldNtt (reverse init twiddles)

theorem reverse_zero (n : ℕ) : reverse n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [reverse,Nat.zero_mod,zero_mul,Nat.zero_div,ih,zero_add]

/-- Reversing concatenated low/high bit blocks exchanges their positions. -/
theorem reverse_append (lowBits highBits low high : ℕ) (bound : low < 2^lowBits) :
    reverse (lowBits+highBits) (low+2^lowBits*high) =
      2^highBits*reverse lowBits low+reverse highBits high := by
  induction lowBits generalizing low with
  | zero => have zero : low = 0 := by simpa using bound
            subst low
            simp only [zero_add,pow_zero,one_mul,reverse,mul_zero]
  | succ lowBits ih =>
    have half : low/2 < 2^lowBits := by rw [pow_succ] at bound; omega
    have even : 2^(lowBits+1)*high = 2*(2^lowBits*high) := by rw [pow_succ]; ring
    have divided : (low+2^(lowBits+1)*high)/2 = low/2+2^lowBits*high := by
      rw [even]
      omega
    have reduced : (low+2^(lowBits+1)*high)%2 = low%2 := by
      rw [even]
      omega
    rw [Nat.succ_add,reverse,divided,reduced,ih _ half,reverse,pow_add]
    ring

theorem reverse_one (n : ℕ) : reverse (n+1) 1 = 2^n := by
  simp [reverse,reverse_zero]

/-- Appending a branch bit gives the next recursion half index. -/
theorem reverse_child (depth half : ℕ) (bit : Bool) :
    reverse (depth+1) (half*2+(if bit then 1 else 0)) =
      (if bit then 1 else 0)*2^depth+reverse depth half := by
  have low (bit : ℕ) (bound : bit < 2) : (half*2+bit)%2 = bit := by omega
  have high (bit : ℕ) (bound : bit < 2) : (half*2+bit)/2 = half := by omega
  cases bit
  · simp only [Bool.false_eq_true,ite_false,reverse,low 0 (by decide),high 0 (by decide)]
  · simp only [ite_true,reverse,low 1 (by decide),high 1 (by decide)]

/-- No two valid write indices alias. -/
theorem reverse_involution (n index : ℕ) (bound : index < 2^n) : reverse n (reverse n index) = index := by
  induction n generalizing index with
  | zero => have zero : index = 0 := by simpa using bound
            subst index
            rfl
  | succ n ih =>
    have half : index/2 < 2^n := by rw [pow_succ] at bound; omega
    have reversed := NativeGoldNtt.reverse_bound n (index/2)
    rw [show reverse (n+1) index = index%2*2^n+reverse n (index/2) from rfl]
    have split : index%2*2^n+reverse n (index/2) = reverse n (index/2)+2^n*(index%2) := by ac_rfl
    rw [split,reverse_append n 1 _ _ reversed,ih _ half]
    simp only [pow_one,reverse,Nat.pow_zero,mul_one,add_zero]
    have bit := Nat.mod_lt index (by decide : 0 < 2)
    rw [Nat.mod_eq_of_lt bit]
    omega

theorem reverse_eq_iff (n left right : ℕ) (leftBound : left < 2^n) (rightBound : right < 2^n) :
    reverse n left = reverse n right ↔ left = right := by
  constructor
  · intro same
    have mapped := congrArg (reverse n) same
    simpa only [reverse_involution n left leftBound,reverse_involution n right rightBound] using mapped
  · rintro rfl
    rfl

/-- Each initialized slot contains its original power, and later distinct
writes cannot overwrite it. Unwritten slots retain literal zero. -/
theorem init_get (log : ℕ) (root : Word) (count index : ℕ) (countBound : count ≤ 2^log) (indexBound : index < 2^log) :
    (init log root count).1[reverse log index]'(by
      rw [NativeGoldNtt.init_length]; exact NativeGoldNtt.reverse_bound _ _) =
      if index < count then NativeGoldSolinas.pow root index else 0 := by
  induction count with
  | zero => simp only [init,List.getElem_replicate,Nat.not_lt_zero,ite_false]
  | succ count ih =>
    have inside : count < 2^log := by omega
    simp only [init,List.getElem_set,NativeGoldNtt.init_power,reverse_eq_iff log count index inside indexBound]
    by_cases same : count = index
    · subst index
      simp only [ite_true,Nat.lt_succ_self]
    · have previous := ih (by omega)
      have before : index < count+1 ↔ index < count := by omega
      simp only [same,ite_false,previous,before]

/-- Actual table lookup is the computed power at the reversed address. -/
theorem twiddles_get (log : ℕ) (root : Word) (index : Fin (2^log)) :
    (twiddles log root)[index.val]'(by rw [NativeGoldNtt.twiddles_length]; exact index.isLt) =
      NativeGoldSolinas.pow root (reverse log index.val) := by
  have reversed := NativeGoldNtt.reverse_bound log index.val
  have entry := init_get log root (2^log) (reverse log index.val) le_rfl reversed
  simpa only [reverse_involution log index.val index.isLt,ite_eq_left reversed,twiddles] using entry

/-- The first twiddle of a subtree has the exact odd-root exponent required
by the semantic radix-two transform, at every recursion depth. -/
theorem subtree_exponent (log depth half : ℕ) (positive : log ≠ 0) (halfBound : half < 2^depth) :
    reverse (log+depth) (2^depth+half) = (2*reverse depth half+1)*2^(log-1) := by
  have split : log = (log-1)+1 := by omega
  rw [Nat.add_comm log depth,show 2^depth+half = half+2^depth*1 by omega,
    reverse_append depth log half 1 halfBound]
  conv_lhs => rhs; rw [split,reverse_one]
  conv_lhs => lhs; lhs; rw [split,pow_succ]
  ring

noncomputable section

theorem twiddles_value (log : ℕ) (root : Word) (index : Fin (2^log)) :
    NativeGoldSolinas.value ((twiddles log root)[index.val]'(by rw [NativeGoldNtt.twiddles_length]; exact index.isLt)) =
      NativeGoldSolinas.value root^(reverse log index.val) := by
  rw [twiddles_get,NativeGoldSolinas.pow_value]

end
end FormalProof4FHE.HasteBoots.NativeGoldNttTwiddles
