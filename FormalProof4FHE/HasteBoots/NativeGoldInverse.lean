module

public import FormalProof4FHE.HasteBoots.NativeGoldArithmetic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

set_option maxRecDepth 4096

/-!
# Raw Goldilocks inversion chain

The native addition chain calls `pow_reduce(1 << N)` only for N=3,6,12,32.
For these powers of two it canonicalizes the base, performs N squarings,
and returns before the general bit loop. This model retains that initial
canonicalization on every `exp_acc` call and each raw multiplication.
Checked Rust control-flow/instruction refinement remains open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldInverse

open NativeFieldRepresentation NativeFields NativeGoldArithmetic

def canonical (word : GoldWord) : GoldWord :=
  ⟨goldCanonical word, (goldCanonical_lt word).trans (by decide)⟩

theorem canonical_value (word : GoldWord) : goldValue (canonical word) = goldValue word :=
  goldCanonical_cast word

def square (word : GoldWord) : GoldWord := mul word word

theorem square_value (word : GoldWord) : goldValue (square word) = goldValue word ^ 2 := by
  simp only [square, mul_value, pow_two]

def squares (n : ℕ) (word : GoldWord) : GoldWord := square^[n] word

theorem squares_value (n : ℕ) (word : GoldWord) :
    goldValue (squares n word) = goldValue word ^ (2 ^ n) := by
  induction n generalizing word with
  | zero => simp only [squares, Function.iterate_zero_apply, pow_zero, pow_one]
  | succ n ih =>
    change goldValue (square^[n + 1] word) = _
    rw [Function.iterate_succ_apply]
    change goldValue (squares n (square word)) = _
    rw [ih, square_value, ← pow_mul, pow_succ]
    congr 1
    omega

def expAcc (n : ℕ) (base tail : GoldWord) : GoldWord :=
  mul (squares n (canonical base)) tail

theorem expAcc_value (n : ℕ) (base tail : GoldWord) :
    goldValue (expAcc n base tail) = goldValue base ^ (2 ^ n) * goldValue tail := by
  rw [expAcc, mul_value, squares_value, canonical_value]

/-- Operation order and canonicalization sites of native `try_inverse`. -/
def chain (word : GoldWord) : GoldWord :=
  let value := canonical word
  let t2 := mul (square value) value
  let t3 := mul (square t2) value
  let t6 := expAcc 3 t3 t3
  let t12 := expAcc 6 t6 t6
  let t24 := expAcc 12 t12 t12
  let t30 := expAcc 6 t24 t6
  let t31 := mul (square t30) value
  let t63 := expAcc 32 t31 t31
  mul (square t63) value

theorem chain_power (word : GoldWord) :
    goldValue (chain word) = goldValue word ^ (goldilocksModulus - 2) := by
  let value := canonical word
  let t2 := mul (square value) value
  let t3 := mul (square t2) value
  let t6 := expAcc 3 t3 t3
  let t12 := expAcc 6 t6 t6
  let t24 := expAcc 12 t12 t12
  let t30 := expAcc 6 t24 t6
  let t31 := mul (square t30) value
  let t63 := expAcc 32 t31 t31
  have hv : goldValue value = goldValue word := canonical_value word
  have h2 : goldValue t2 = goldValue word ^ 3 := by
    change goldValue (mul (square value) value) = _
    rw [mul_value, square_value, hv, ← pow_succ]
  have h3 : goldValue t3 = goldValue word ^ 7 := by
    change goldValue (mul (square t2) value) = _
    rw [mul_value, square_value, h2, hv, ← pow_mul, ← pow_succ]
  have h6 : goldValue t6 = goldValue word ^ 63 := by
    change goldValue (expAcc 3 t3 t3) = _
    rw [expAcc_value, h3, ← pow_mul, ← pow_add]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  have h12 : goldValue t12 = goldValue word ^ 4095 := by
    change goldValue (expAcc 6 t6 t6) = _
    rw [expAcc_value, h6, ← pow_mul, ← pow_add]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  have h24 : goldValue t24 = goldValue word ^ 16777215 := by
    change goldValue (expAcc 12 t12 t12) = _
    rw [expAcc_value, h12, ← pow_mul, ← pow_add]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  have h30 : goldValue t30 = goldValue word ^ 1073741823 := by
    change goldValue (expAcc 6 t24 t6) = _
    rw [expAcc_value, h24, h6, ← pow_mul, ← pow_add]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  have h31 : goldValue t31 = goldValue word ^ 2147483647 := by
    change goldValue (mul (square t30) value) = _
    rw [mul_value, square_value, h30, hv, ← pow_mul, ← pow_succ]
  have h63 : goldValue t63 = goldValue word ^ 9223372034707292159 := by
    change goldValue (expAcc 32 t31 t31) = _
    rw [expAcc_value, h31, ← pow_mul, ← pow_add]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  change goldValue (mul (square t63) value) = _
  rw [mul_value, square_value, h63, hv, ← pow_mul, ← pow_succ]
  norm_num only [goldilocksModulus, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]


theorem chain_inverse (word : GoldWord) (nonzero : goldValue word ≠ 0) :
    goldValue (chain word) = (goldValue word)⁻¹ := by
  rw [chain_power]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, show goldilocksModulus - 2 + 1 = goldilocksModulus - 1 by decide]
  exact ZMod.pow_card_sub_one_eq_one nonzero

def tryInverse (word : GoldWord) : Option GoldWord :=
  if goldCanonical word = 0 then none else some (chain word)

theorem canonical_zero_iff (word : GoldWord) : goldCanonical word = 0 ↔ goldValue word = 0 := by
  constructor
  · intro zero
    rw [← goldCanonical_cast, zero, Nat.cast_zero]
  · intro zero
    have values := congrArg (fun value : Goldilocks => value.val) zero
    simpa only [goldValue_val, ZMod.val_zero] using values

theorem tryInverse_none (word : GoldWord) : tryInverse word = none ↔ goldValue word = 0 := by
  simp only [tryInverse, ite_eq_left_iff, Option.some_ne_none, imp_false, not_not, canonical_zero_iff]

theorem tryInverse_value (word : GoldWord) :
    (tryInverse word).map goldValue =
      if goldValue word = 0 then none else some (goldValue word)⁻¹ := by
  unfold tryInverse
  split
  next zero => simp only [(canonical_zero_iff word).mp zero, ite_true, Option.map_none]
  next nonzero =>
    have nz := mt (canonical_zero_iff word).mpr nonzero
    simp only [nz, ite_false, Option.map_some, chain_inverse word nz]

end FormalProof4FHE.HasteBoots.NativeGoldInverse
