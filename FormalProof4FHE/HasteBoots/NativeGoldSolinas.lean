module

public import FormalProof4FHE.HasteBoots.NativeGoldArithmetic

@[expose] public section

/-! Canonical Goldilocks arithmetic of concrete-ntt's `PrimeModulus for Solinas`
at cdeba793e46208320b30d78be19f7be78d49016a. The scalar kernel's add/subtract
branches and wrapped wide-product reduction are retained. These are different
stored representatives from the lazy algebra arithmetic. Rust instructions
and SIMD-lane refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldSolinas

open NativeFields NativeFieldRepresentation
open NativeGoldArithmetic (WideWord low highHigh highLow)

abbrev Word := Fin goldilocksModulus

def raw (word : Word) : GoldWord := ⟨word.val,word.isLt.trans (by decide)⟩
def canonical (word : GoldWord) : Word := ⟨goldCanonical word,goldCanonical_lt word⟩
def value (word : Word) : Goldilocks := (word.val : Goldilocks)

theorem canonical_value (word : GoldWord) : value (canonical word) = goldValue word := goldCanonical_cast word

def addRaw (left right : Word) : ℕ :=
  if goldilocksModulus-right.val ≤ left.val then left.val-(goldilocksModulus-right.val) else left.val+right.val

theorem add_spec (left right : Word) : addRaw left right < goldilocksModulus ∧
    addRaw left right + (if goldilocksModulus ≤ left.val+right.val then goldilocksModulus else 0) = left.val+right.val := by
  have l := left.isLt
  have r := right.isLt
  unfold addRaw
  split_ifs <;> omega

def add (left right : Word) : Word := ⟨addRaw left right,(add_spec left right).1⟩

def subRaw (left right : Word) : ℕ :=
  if right.val ≤ left.val then left.val-right.val else left.val+(goldilocksModulus-right.val)

theorem sub_spec (left right : Word) : subRaw left right < goldilocksModulus ∧
    subRaw left right + right.val = left.val + (if left.val < right.val then goldilocksModulus else 0) := by
  have l := left.isLt
  have r := right.isLt
  unfold subRaw
  split_ifs <;> omega

def sub (left right : Word) : Word := ⟨subRaw left right,(sub_spec left right).1⟩

/-- lo.wrapping_sub(hi), followed by the conditional wrapping addition of p. -/
def low2 (word : WideWord) : ℕ :=
  let difference := (low word+wordModulus-highHigh word)%wordModulus
  if low word < highHigh word then (difference+goldilocksModulus)%wordModulus else difference

/-- `(mid << 32) - mid`; both operations fit the native u64. -/
def product (word : WideWord) : ℕ := highLow word*radix-highLow word

def reduceRaw (word : WideWord) : ℕ :=
  let result := (low2 word+product word)%wordModulus
  if result < product word ∨ goldilocksModulus ≤ result then
    (result+wordModulus-goldilocksModulus)%wordModulus
  else result

/-- Both wrap corrections compute the unique canonical representative. -/
theorem reduce_spec (word : WideWord) :
    low2 word = NativeGoldArithmetic.reduceLow word ∧
    product word = highLow word*NativeGoldArithmetic.epsilon ∧
    reduceRaw word < goldilocksModulus ∧
    reduceRaw word + (if goldilocksModulus ≤ low2 word+product word then goldilocksModulus else 0) =
      low2 word+product word := by
  have bound := word.isLt
  unfold reduceRaw low2 product NativeGoldArithmetic.reduceLow low highHigh highLow
    wordModulus radix NativeGoldArithmetic.epsilon goldilocksModulus at *
  norm_num only [Nat.reducePow] at bound ⊢
  split_ifs <;> omega

def reduce (word : WideWord) : Word := ⟨reduceRaw word,(reduce_spec word).2.2.1⟩

def mul (left right : Word) : Word := reduce (NativeGoldArithmetic.mulWide (raw left) (raw right))

def pow (word : Word) : ℕ → Word
  | 0 => ⟨1,by decide⟩
  | n+1 => mul (pow word n) word

noncomputable section

theorem add_value (left right : Word) : value (add left right) = value left+value right := by
  have equation := congrArg (fun n : ℕ => (n : Goldilocks)) (add_spec left right).2
  simp only [Nat.cast_add] at equation
  have zero (condition : Prop) [Decidable condition] :
      ((if condition then goldilocksModulus else 0 : ℕ) : Goldilocks) = 0 := by
    split <;> simp only [ZMod.natCast_self,Nat.cast_zero]
  rw [zero,add_zero] at equation
  exact equation

theorem sub_value (left right : Word) : value (sub left right) = value left-value right := by
  have equation := congrArg (fun n : ℕ => (n : Goldilocks)) (sub_spec left right).2
  simp only [Nat.cast_add] at equation
  have zero (condition : Prop) [Decidable condition] :
      ((if condition then goldilocksModulus else 0 : ℕ) : Goldilocks) = 0 := by
    split <;> simp only [ZMod.natCast_self,Nat.cast_zero]
  rw [zero,add_zero] at equation
  exact eq_sub_of_add_eq equation

theorem reduce_value (word : WideWord) : value (reduce word) = (word.val : Goldilocks) := by
  have spec := reduce_spec word
  have equation := congrArg (fun n : ℕ => (n : Goldilocks)) spec.2.2.2
  have first := congrArg (fun n : ℕ => (n : Goldilocks)) (NativeGoldArithmetic.reduce_bounds word).2.2.2.1
  have whole := congrArg (fun n : ℕ => (n : Goldilocks)) (NativeGoldArithmetic.wide_decomposition word)
  have zero (condition : Prop) [Decidable condition] :
      ((if condition then goldilocksModulus else 0 : ℕ) : Goldilocks) = 0 := by
    split <;> simp only [ZMod.natCast_self,Nat.cast_zero]
  rw [spec.1,spec.2.1] at equation
  simp only [Nat.cast_add,Nat.cast_mul] at equation first whole
  rw [zero,add_zero] at equation first
  have constants : (wordModulus : Goldilocks) = (NativeGoldArithmetic.epsilon : Goldilocks) ∧
      (radix : Goldilocks)*(NativeGoldArithmetic.epsilon : Goldilocks) = -1 := by decide +kernel
  rw [constants.1] at whole
  change (reduceRaw word : Goldilocks) = _
  linear_combination equation + first + whole - (highHigh word : Goldilocks)*constants.2

theorem mul_value (left right : Word) : value (mul left right) = value left*value right := by
  simpa only [mul,NativeGoldArithmetic.mulWide,raw,Nat.cast_mul,value] using
    reduce_value (NativeGoldArithmetic.mulWide (raw left) (raw right))

theorem pow_value (word : Word) (n : ℕ) : value (pow word n) = value word^n := by
  induction n with
  | zero => simp only [pow,value,pow_zero,Nat.cast_one]
  | succ n ih => rw [pow,mul_value,ih,pow_succ]

end
end FormalProof4FHE.HasteBoots.NativeGoldSolinas
