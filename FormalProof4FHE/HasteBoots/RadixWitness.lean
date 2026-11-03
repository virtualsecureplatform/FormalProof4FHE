module

public import FormalProof4FHE.HasteBoots.RadixCanonicity

@[expose] public section

/-!
# Honest radix-decomposition digits and borrow witnesses

Borrow computation follows the native low-to-high recurrence. Its final bit
is zero exactly when the bounded digit string plus its incoming bit is below
the public bound. Canonical field digits therefore construct valid linear and
lookup witnesses. These are arithmetic witnesses, not a complete honest
cryptographic prover or a Rust/scheduler/Fiat--Shamir refinement.
-/

namespace FormalProof4FHE.HasteBoots.RadixWitness

noncomputable section

open RadixCanonicity

def next (digit bound incoming : ℕ) : ℕ := if bound < digit + incoming then 1 else 0

theorem next_bit (digit bound incoming : ℕ) : next digit bound incoming ≤ 1 := by
  unfold next
  split_ifs <;> omega

def sequence : {d : ℕ} → (Fin d → ℕ) → (Fin d → ℕ) → ℕ → Fin (d + 1) → ℕ
  | 0, _, _, incoming => fun _ => incoming
  | _ + 1, digits, bounds, incoming =>
      Fin.cases incoming (sequence (fun i => digits i.succ) (fun i => bounds i.succ)
        (next (digits 0) (bounds 0) incoming))

theorem sequence_zero {d : ℕ} (digits bounds : Fin d → ℕ) (incoming : ℕ) :
    sequence digits bounds incoming 0 = incoming := by cases d <;> rfl

theorem sequence_succ {d : ℕ} (digits bounds : Fin (d + 1) → ℕ) (incoming : ℕ) (i : Fin (d + 1)) :
    sequence digits bounds incoming i.succ =
      sequence (fun j => digits j.succ) (fun j => bounds j.succ) (next (digits 0) (bounds 0) incoming) i := rfl

theorem sequence_bit {d : ℕ} (digits bounds : Fin d → ℕ) (incoming : ℕ) (bit : incoming ≤ 1)
    (i : Fin (d + 1)) : sequence digits bounds incoming i ≤ 1 := by
  induction d generalizing incoming with
  | zero => exact bit
  | succ d ih =>
    refine Fin.cases bit (fun j => ?_) i
    exact ih _ _ _ (next_bit _ _ _) j

theorem sequence_step {d : ℕ} (digits bounds : Fin d → ℕ) (incoming : ℕ) (i : Fin d) :
    sequence digits bounds incoming i.succ =
      next (digits i) (bounds i) (sequence digits bounds incoming i.castSucc) := by
  induction d generalizing incoming with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.castSucc_zero, sequence_zero, sequence_succ, sequence_zero]
    · simpa only [← Fin.succ_castSucc, sequence_succ] using ih _ _ _ j

theorem comparison_step {radix digit bound incoming lowDigit lowBound : ℕ}
    (digitSmall : digit < radix) (boundSmall : bound < radix) (bit : incoming ≤ 1) :
    digit + radix * lowDigit + incoming ≤ bound + radix * lowBound ↔
      lowDigit + next digit bound incoming ≤ lowBound := by
  unfold next
  split_ifs with overflow
  · constructor
    · intro whole
      by_contra wrong
      have : lowBound ≤ lowDigit := by omega
      nlinarith [Nat.mul_le_mul_left radix this]
    · intro tail
      nlinarith [Nat.mul_le_mul_left radix tail]
  · constructor
    · intro whole
      by_contra wrong
      have : lowBound + 1 ≤ lowDigit := by omega
      nlinarith [Nat.mul_le_mul_left radix this]
    · intro tail
      nlinarith [Nat.mul_le_mul_left radix tail]

/-- Completeness and rejection of the actual computed final borrow. -/
theorem last_zero_iff {radix d : ℕ} (digits bounds : Fin d → ℕ)
    (digitSmall : ∀ i, digits i < radix) (boundSmall : ∀ i, bounds i < radix)
    (incoming : ℕ) (bit : incoming ≤ 1) :
    sequence digits bounds incoming (Fin.last d) = 0 ↔
      value radix digits + incoming ≤ value radix bounds := by
  induction d generalizing incoming with
  | zero => simp [sequence, value]
  | succ d ih =>
    change sequence (fun i : Fin d => digits i.succ) (fun i : Fin d => bounds i.succ)
      (next (digits 0) (bounds 0) incoming) (Fin.last d) = 0 ↔ _
    rw [ih _ _ (fun i => digitSmall i.succ) (fun i => boundSmall i.succ) _ (next_bit _ _ _),
      value_succ, value_succ]
    exact (comparison_step (digitSmall 0) (boundSmall 0) bit).symm

/-- The native zero padding borrows agree with the recurrence on zero digits. -/
theorem sequence_zero_digits {d : ℕ} (bounds : Fin d → ℕ) :
    sequence (fun _ => 0) bounds 0 = fun _ => 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    change sequence (fun _ : Fin d => 0) (fun i => bounds i.succ) (next 0 (bounds 0) 0) j = 0
    simpa only [next, zero_add, Nat.not_lt_zero, reduceIte] using congrFun (ih (fun i => bounds i.succ)) j

theorem sequence_table {p radix d : ℕ} (digits bounds : Fin d → ℕ)
    (small : ∀ i, digits i < radix) (incoming : ℕ) (bit : incoming ≤ 1) (i : Fin d) :
    ![(digits i : ZMod p), (sequence digits bounds incoming i.castSucc : ZMod p),
      (sequence digits bounds incoming i.succ : ZMod p)] ∈ table p radix (bounds i) := by
  apply (mem_table_iff p radix (bounds i) _).mpr
  refine ⟨⟨digits i, small i⟩, ⟨sequence digits bounds incoming i.castSucc, ?_⟩, ?_⟩
  · have := sequence_bit digits bounds incoming bit i.castSucc
    omega
  · rw [sequence_step]
    rfl

def digits (radix d x : ℕ) (i : Fin d) : ℕ := x / radix ^ i.val % radix

def borrows (p radix d x : ℕ) : Fin (d + 1) → ℕ :=
  sequence (digits radix d x) (fun i => modulusDigit p radix i.val) 0

theorem digits_small {radix d x : ℕ} (radixLarge : 1 < radix) (i : Fin d) :
    digits radix d x i < radix := Nat.mod_lt _ (by omega)

theorem digits_value {radix d x : ℕ} (range : x < radix ^ d) :
    value radix (digits radix d x) = x := by
  change value radix (fun i : Fin d => x / radix ^ i.val % radix) = x
  simpa only [Nat.div_eq_of_lt range, mul_zero, add_zero] using value_mod_digits radix x d

theorem borrows_first (p radix d x : ℕ) : borrows p radix d x 0 = 0 :=
  sequence_zero _ _ _

theorem borrows_bit (p radix d x : ℕ) (i : Fin (d + 1)) : borrows p radix d x i ≤ 1 :=
  sequence_bit _ _ _ (by decide) i

theorem borrows_last {p radix d x : ℕ} (radixLarge : 1 < radix) (range : x < p)
    (enough : p - 1 < radix ^ d) : borrows p radix d x (Fin.last d) = 0 := by
  apply (last_zero_iff (digits radix d x) (fun i => modulusDigit p radix i.val)
    (digits_small radixLarge) (fun _ => Nat.mod_lt _ (by omega)) 0 (by decide)).mpr
  rw [digits_value (by omega), modulus_value p radix d enough, add_zero]
  omega

theorem borrows_zero (p radix d : ℕ) : borrows p radix d 0 = fun _ => 0 := by
  unfold borrows
  have zeroDigits : digits radix d 0 = fun _ => 0 := by funext i; simp [digits]
  rw [zeroDigits]
  exact sequence_zero_digits _

/-- Natural witnesses in the literal native registry: source, digits, borrows. -/
def columns (p radix d x : ℕ) (factor : Fin (2 * d + 2)) : ℕ :=
  if zero : factor.val = 0 then x
  else if digit : factor.val ≤ d then digits radix d x ⟨factor.val - 1, by omega⟩
  else borrows p radix d x ⟨factor.val - (d + 1), by have := factor.isLt; omega⟩

theorem columns_input (p radix d x : ℕ) : columns p radix d x DecompositionLinear.input = x := by
  simp [columns, DecompositionLinear.input]

theorem columns_digit (p radix d x : ℕ) (i : Fin d) :
    columns p radix d x (DecompositionLinear.digit i) = digits radix d x i := by
  have small : i.val + 1 ≤ d := by have := i.isLt; omega
  simp [columns, DecompositionLinear.digit, small]

theorem columns_borrow (p radix d x : ℕ) (i : Fin (d + 1)) :
    columns p radix d x (DecompositionLinear.borrow i) = borrows p radix d x i := by
  have outside : ¬d + 1 + i.val ≤ d := by omega
  simp [columns, DecompositionLinear.borrow, outside]

theorem columns_zero (p radix d : ℕ) (factor : Fin (2 * d + 2)) : columns p radix d 0 factor = 0 := by
  unfold columns
  split_ifs
  · rfl
  · simp [digits]
  · rw [borrows_zero]

def tables (p radix d : ℕ) {n b : ℕ} (source : MatrixFold.Cube n → Fin b → ZMod p)
    (factor : Fin (2 * d + 2)) (cell : MatrixFold.Cube n) (lane : Fin b) : ZMod p :=
  (columns p radix d (source cell lane).val factor : ZMod p)

theorem tables_zero {p radix d n b : ℕ} (source : MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) (zero : source cell lane = 0) (factor : Fin (2 * d + 2)) :
    tables p radix d source factor cell lane = 0 := by
  simp only [tables, zero, ZMod.val_zero, columns_zero, Nat.cast_zero]

variable {p radix d n b : ℕ} [Fact p.Prime]

theorem tables_input (source : MatrixFold.Cube n → Fin b → ZMod p) (cell : MatrixFold.Cube n) (lane : Fin b) :
    tables p radix d source DecompositionLinear.input cell lane = source cell lane := by
  simp only [tables, columns_input, ZMod.natCast_zmod_val]

/-- Canonical digits and computed borrows satisfy every linear constraint,
including padding cells when their input is zero. -/
theorem tables_valid (radixLarge : 1 < radix) (enough : p - 1 < radix ^ d)
    (source : MatrixFold.Cube n → Fin b → ZMod p) :
    DecompositionLinear.Relation (radix : ZMod p) (tables p radix d source) := by
  intro cell lane
  have range : (source cell lane).val < radix ^ d := by
    have := (source cell lane).val_lt
    omega
  have reconstruct := congrArg (fun v : ℕ => (v : ZMod p)) (digits_value range)
  simp only [value, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val] at reconstruct
  refine ⟨?_, ?_, ?_⟩
  · simpa only [tables, columns_input, columns_digit, digits, ZMod.natCast_zmod_val] using reconstruct.symm
  · simp only [tables, DecompositionLinear.firstBorrow, columns_borrow]
    change (borrows p radix d (source cell lane).val 0 : ZMod p) = 0
    rw [borrows_first, Nat.cast_zero]
  · simp only [tables, DecompositionLinear.lastBorrow, columns_borrow]
    change (borrows p radix d (source cell lane).val (Fin.last d) : ZMod p) = 0
    rw [borrows_last radixLarge (source cell lane).val_lt enough, Nat.cast_zero]

omit [Fact p.Prime] in
/-- Membership is constructed in the concrete public tables at each active
position; it is not supplied as an honest-prover premise. -/
theorem tables_lookup (radixLarge : 1 < radix) (source : MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) :
    LookupAt p radix (tables p radix d source) cell lane := by
  intro i
  simpa only [tables, columns_digit, columns_borrow, borrows] using
    (sequence_table (p := p) (digits radix d (source cell lane).val)
      (fun i => modulusDigit p radix i.val) (digits_small radixLarge) 0 (by decide) i)

/-- The arithmetic witness constructor supplies the actual relations and
local checked values. Honest opening/scheduler completion remains separate. -/
theorem honest_check [DecidableEq (ZMod p)] (radixLarge : 1 < radix) (enough : p - 1 < radix ^ d)
    (source : MatrixFold.Cube n → Fin b → ZMod p) (query : PackedSumcheckSubclaim.Query (ZMod p) b n) :
    PackedLinear.check (DecompositionLinear.relations (d := d) (radix : ZMod p))
      (fun factor => query.fold (tables p radix d source factor)) = true :=
  DecompositionLinear.honest_check _ _ (tables_valid radixLarge enough source) query

/-- Arithmetic completeness supplies a witness with the original input slot,
all linear constraints and all public comparison memberships. -/
theorem exists_witness (radixLarge : 1 < radix) (enough : p - 1 < radix ^ d)
    (source : MatrixFold.Cube n → Fin b → ZMod p) :
    ∃ witness : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → ZMod p,
      (∀ cell lane, witness DecompositionLinear.input cell lane = source cell lane) ∧
      DecompositionLinear.Relation (radix : ZMod p) witness ∧
      ∀ cell lane, LookupAt p radix witness cell lane :=
  ⟨tables p radix d source, tables_input source, tables_valid radixLarge enough source, tables_lookup radixLarge source⟩

theorem exists_witness_digitCount (radixLarge : 1 < radix)
    (source : MatrixFold.Cube n → Fin b → ZMod p) :
    ∃ witness : Fin (2 * digitCount p radix + 2) → MatrixFold.Cube n → Fin b → ZMod p,
      (∀ cell lane, witness DecompositionLinear.input cell lane = source cell lane) ∧
      DecompositionLinear.Relation (radix : ZMod p) witness ∧
      ∀ cell lane, LookupAt p radix witness cell lane :=
  exists_witness radixLarge (digitCount_enough p radix radixLarge) source

end

end FormalProof4FHE.HasteBoots.RadixWitness
