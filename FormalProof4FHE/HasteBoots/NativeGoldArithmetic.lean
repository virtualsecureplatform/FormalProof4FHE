module

public import FormalProof4FHE.HasteBoots.NativeFieldRepresentation

@[expose] public section

/-!
# Lazy Goldilocks addition, subtraction and negation

The natural-word computations retain the exact two carry/borrow correction
steps in `modulus/goldilocks/ops.rs`. Every u64 input is permitted, including
lazy representatives. No canonicalization is inserted before addition or
subtraction. Rust instruction refinement remains a separate obligation.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldArithmetic

open NativeFieldRepresentation NativeFields

def epsilon : ℕ := 4294967295

def addLow (left right : GoldWord) : ℕ := (left.val + right.val) % wordModulus

def addCorrection (left right : GoldWord) : ℕ :=
  if wordModulus ≤ left.val + right.val then epsilon else 0

def addRaw (left right : GoldWord) : ℕ :=
  let corrected := addLow left right + addCorrection left right
  corrected % wordModulus + if wordModulus ≤ corrected then epsilon else 0

theorem add_bounds (left right : GoldWord) :
    addRaw left right < 2 ^ 64 ∧
    addRaw left right +
      (if wordModulus ≤ left.val + right.val then goldilocksModulus else 0) +
      (if wordModulus ≤ addLow left right + addCorrection left right then goldilocksModulus else 0) =
      left.val + right.val := by
  have l := left.isLt
  have r := right.isLt
  unfold addRaw addLow addCorrection wordModulus epsilon goldilocksModulus at *
  norm_num only [Nat.reducePow] at l r ⊢
  split_ifs <;> omega

def add (left right : GoldWord) : GoldWord := ⟨addRaw left right, (add_bounds left right).1⟩

theorem add_value (left right : GoldWord) :
    goldValue (add left right) = goldValue left + goldValue right := by
  have equation := congrArg (fun n : ℕ => (n : Goldilocks)) (add_bounds left right).2
  simp only [Nat.cast_add] at equation
  have zero (condition : Prop) [Decidable condition] :
      ((if condition then goldilocksModulus else 0 : ℕ) : Goldilocks) = 0 := by
    split <;> simp only [ZMod.natCast_self, Nat.cast_zero]
  rw [zero, zero, add_zero, add_zero] at equation
  exact equation

def subLow (left right : GoldWord) : ℕ := (left.val + wordModulus - right.val) % wordModulus

def subCorrection (left right : GoldWord) : ℕ :=
  if left.val < right.val then epsilon else 0

def subRaw (left right : GoldWord) : ℕ :=
  let low := subLow left right
  let correction := subCorrection left right
  let corrected := (low + wordModulus - correction) % wordModulus
  if low < correction then corrected - epsilon else corrected

theorem sub_bounds (left right : GoldWord) :
    subRaw left right < 2 ^ 64 ∧
    subRaw left right + right.val = left.val +
      (if left.val < right.val then goldilocksModulus else 0) +
      (if subLow left right < subCorrection left right then goldilocksModulus else 0) := by
  have l := left.isLt
  have r := right.isLt
  unfold subRaw subLow subCorrection wordModulus epsilon goldilocksModulus at *
  norm_num only [Nat.reducePow] at l r ⊢
  split_ifs <;> omega

def sub (left right : GoldWord) : GoldWord := ⟨subRaw left right, (sub_bounds left right).1⟩

theorem sub_value (left right : GoldWord) :
    goldValue (sub left right) = goldValue left - goldValue right := by
  have equation := congrArg (fun n : ℕ => (n : Goldilocks)) (sub_bounds left right).2
  simp only [Nat.cast_add] at equation
  have zero (condition : Prop) [Decidable condition] :
      ((if condition then goldilocksModulus else 0 : ℕ) : Goldilocks) = 0 := by
    split <;> simp only [ZMod.natCast_self, Nat.cast_zero]
  rw [zero, zero, add_zero, add_zero] at equation
  exact eq_sub_of_add_eq equation

def negRaw (word : GoldWord) : ℕ :=
  if goldCanonical word = 0 then 0 else goldilocksModulus - goldCanonical word

theorem neg_bound (word : GoldWord) : negRaw word < goldilocksModulus := by
  have bound := goldCanonical_lt word
  unfold negRaw
  split <;> omega

def neg (word : GoldWord) : GoldWord :=
  ⟨negRaw word, (neg_bound word).trans (by decide)⟩

theorem neg_canonical (word : GoldWord) : (neg word).val < goldilocksModulus := neg_bound word

theorem neg_value (word : GoldWord) : goldValue (neg word) = -goldValue word := by
  change (negRaw word : Goldilocks) = _
  unfold negRaw
  split
  next zero =>
    have value := goldCanonical_cast word
    rw [zero, Nat.cast_zero] at value
    simp only [Nat.cast_zero, ← value, neg_zero]
  next =>
    rw [Nat.cast_sub (Nat.le_of_lt (goldCanonical_lt word)), ZMod.natCast_self,
      zero_sub, goldCanonical_cast]

/-- Unsigned halves used by the native u128 reduction. -/
abbrev WideWord := Fin (2 ^ 128)

def low (word : WideWord) : ℕ := word.val % wordModulus
def highHigh (word : WideWord) : ℕ := word.val / wordModulus / radix
def highLow (word : WideWord) : ℕ := word.val / wordModulus % radix

def reduceLow (word : WideWord) : ℕ :=
  (low word + wordModulus - highHigh word) % wordModulus -
    if low word < highHigh word then epsilon else 0

def reduceRaw (word : WideWord) : ℕ :=
  let total := reduceLow word + highLow word * epsilon
  total % wordModulus + if wordModulus ≤ total then epsilon else 0

/-- Both unchecked correction sites in `reduce128` satisfy their native
no-underflow/no-overflow requirements, even for the largest u128. -/
theorem reduce_bounds (word : WideWord) :
    (low word < highHigh word →
      epsilon ≤ (low word + wordModulus - highHigh word) % wordModulus) ∧
    reduceLow word + highLow word * epsilon < wordModulus + goldilocksModulus ∧
    reduceRaw word < 2 ^ 64 ∧
    reduceLow word + highHigh word = low word +
      (if low word < highHigh word then goldilocksModulus else 0) ∧
    reduceRaw word +
      (if wordModulus ≤ reduceLow word + highLow word * epsilon then goldilocksModulus else 0) =
      reduceLow word + highLow word * epsilon := by
  have bound := word.isLt
  unfold reduceRaw reduceLow low highHigh highLow wordModulus radix epsilon goldilocksModulus at *
  norm_num only [Nat.reducePow] at bound ⊢
  split_ifs <;> omega

def reduce (word : WideWord) : GoldWord := ⟨reduceRaw word, (reduce_bounds word).2.2.1⟩

theorem wide_decomposition (word : WideWord) :
    low word + wordModulus * (highLow word + radix * highHigh word) = word.val := by
  have halves := Nat.mod_add_div word.val wordModulus
  have quarters := Nat.mod_add_div (word.val / wordModulus) radix
  unfold low highLow highHigh
  rw [quarters]
  exact halves

private theorem field_constants :
    (wordModulus : Goldilocks) = (epsilon : Goldilocks) ∧
    (radix : Goldilocks) * (epsilon : Goldilocks) = -1 := by decide +kernel

theorem reduce_value (word : WideWord) : goldValue (reduce word) = (word.val : Goldilocks) := by
  have first := congrArg (fun n : ℕ => (n : Goldilocks)) (reduce_bounds word).2.2.2.1
  have second := congrArg (fun n : ℕ => (n : Goldilocks)) (reduce_bounds word).2.2.2.2
  have whole := congrArg (fun n : ℕ => (n : Goldilocks)) (wide_decomposition word)
  have zero (condition : Prop) [Decidable condition] :
      ((if condition then goldilocksModulus else 0 : ℕ) : Goldilocks) = 0 := by
    split <;> simp only [ZMod.natCast_self, Nat.cast_zero]
  simp only [Nat.cast_add, Nat.cast_mul] at first second whole
  rw [zero, add_zero] at first second
  rw [field_constants.1] at whole
  have product := field_constants.2
  change (reduceRaw word : Goldilocks) = _
  calc
    (reduceRaw word : Goldilocks) = (low word : Goldilocks) +
        (highLow word : Goldilocks) * (epsilon : Goldilocks) - (highHigh word : Goldilocks) := by
      linear_combination first + second
    _ = (word.val : Goldilocks) := by
      linear_combination whole - (highHigh word : Goldilocks) * product

def mulWide (left right : GoldWord) : WideWord :=
  ⟨left.val * right.val, by
    have l := left.isLt
    have r := right.isLt
    have h := Nat.mul_lt_mul_of_lt_of_lt l r
    norm_num at h ⊢
    exact h⟩

def mul (left right : GoldWord) : GoldWord := reduce (mulWide left right)

theorem mul_value (left right : GoldWord) :
    goldValue (mul left right) = goldValue left * goldValue right := by
  simpa only [mul, mulWide, Nat.cast_mul, goldValue] using reduce_value (mulWide left right)

/-- Left-to-right addition accumulates from raw zero without normalization. -/
def sum (values : List GoldWord) : GoldWord := values.foldl add 0

private theorem fold_value (values : List GoldWord) (initial : GoldWord) :
    goldValue (values.foldl add initial) = goldValue initial + (values.map goldValue).sum := by
  induction values generalizing initial with
  | nil => simp
  | cons word tail ih => simp only [List.foldl_cons, ih, add_value, List.map_cons, List.sum_cons, add_assoc]

/-- The exact raw left-to-right addition fold, with an arbitrary accumulator. -/
theorem fold_add_value (values : List GoldWord) (initial : GoldWord) :
    goldValue (values.foldl add initial) = goldValue initial + (values.map goldValue).sum :=
  fold_value values initial

theorem sum_value (values : List GoldWord) : goldValue (sum values) = (values.map goldValue).sum := by
  simpa only [sum, goldValue, Fin.val_zero, Nat.cast_zero, zero_add] using fold_value values 0

end FormalProof4FHE.HasteBoots.NativeGoldArithmetic
