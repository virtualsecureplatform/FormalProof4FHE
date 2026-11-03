module

public import FormalProof4FHE.HasteBoots.DecompositionLinear
public import Mathlib.Data.Nat.Digits.Defs

@[expose] public section

/-!
# Integer meaning of canonical radix-decomposition constraints

The native comparison table enumerates digits in [0,radix), incoming borrow
bits and their computed outgoing borrow. Membership supplies integer facts,
without interpreting arbitrary field congruences as integer equalities.
Weighted borrow inequalities telescope; zero endpoints bound reconstructed
digits by p-1. Combined with the trusted linear relation this identifies the
integer reconstruction with the input field element's canonical representative.
Lookup-verifier enforcement, native configuration/normalization and complete
PBS/Fiat--Shamir refinement are separate obligations.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.RadixCanonicity

noncomputable section

def value (radix : ℕ) {d : ℕ} (digits : Fin d → ℕ) : ℕ :=
  ∑ i, radix ^ i.val * digits i

theorem value_succ (radix : ℕ) {d : ℕ} (digits : Fin (d + 1) → ℕ) :
    value radix digits = digits 0 + radix * value radix (fun i => digits i.succ) := by
  simp only [value, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul,
    Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem value_last (radix : ℕ) {d : ℕ} (digits : Fin (d + 1) → ℕ) :
    value radix digits = value radix (fun i => digits i.castSucc) + radix ^ d * digits (Fin.last d) := by
  simp only [value, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem value_eq_ofDigits (radix : ℕ) {d : ℕ} (digits : Fin d → ℕ) :
    value radix digits = Nat.ofDigits radix (List.ofFn digits) := by
  induction d with
  | zero => simp [value]
  | succ d ih => rw [value_succ, List.ofFn_succ, Nat.ofDigits_cons, ← ih]

theorem digits_unique {radix d : ℕ} (radixLarge : 1 < radix) (digits other : Fin d → ℕ)
    (small : ∀ i, digits i < radix) (otherSmall : ∀ i, other i < radix)
    (equal : value radix digits = value radix other) : digits = other := by
  apply List.ofFn_injective
  apply Nat.ofDigits_inj_of_len_eq radixLarge (by simp)
  · intro a member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact small i
  · intro a member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact otherSmall i
  · simpa only [← value_eq_ofDigits] using equal

theorem value_lt_pow {radix d : ℕ} (radixLarge : 1 < radix) (digits : Fin d → ℕ)
    (small : ∀ i, digits i < radix) : value radix digits < radix ^ d := by
  have bound := Nat.ofDigits_lt_base_pow_length radixLarge (l := List.ofFn digits) (by
    intro a member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact small i)
  simpa only [← value_eq_ofDigits, List.length_ofFn] using bound

/-- Local borrow inequalities suffice, with no arithmetic modulo p. -/
theorem weighted_bound (radix : ℕ) (d : ℕ) (digits bounds : Fin d → ℕ) (borrows : Fin (d + 1) → ℕ)
    (step : ∀ i : Fin d, digits i + borrows i.castSucc ≤ bounds i + radix * borrows i.succ) :
    value radix digits + borrows 0 ≤ value radix bounds + radix ^ d * borrows (Fin.last d) := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    have tail := ih (fun i => digits i.succ) (fun i => bounds i.succ) (fun i => borrows i.succ)
      (fun i => step i.succ)
    have first := step 0
    rw [value_succ, value_succ, pow_succ]
    change digits 0 + borrows 0 ≤ bounds 0 + radix * borrows 1 at first
    change value radix (fun i : Fin d => digits i.succ) + borrows 1 ≤
      value radix (fun i : Fin d => bounds i.succ) + radix ^ d * borrows (Fin.last (d + 1)) at tail
    nlinarith [Nat.mul_le_mul_left radix tail]

def modulusDigit (p radix i : ℕ) : ℕ := (p - 1) / radix ^ i % radix

/-- Quotient/remainder telescoping, valid even at zero radix or zero digits. -/
theorem value_mod_digits (radix x d : ℕ) :
    value radix (fun i : Fin d => x / radix ^ i.val % radix) + radix ^ d * (x / radix ^ d) = x := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    rw [value_last]
    have split := Nat.mod_add_div (x / radix ^ d) radix
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at split
    change value radix (fun i : Fin d => x / radix ^ i.val % radix) +
      radix ^ d * (x / radix ^ d % radix) + radix ^ (d + 1) * (x / radix ^ (d + 1)) = x
    rw [pow_succ]
    rw [pow_succ] at split
    nlinarith [congrArg (fun v => radix ^ d * v) split]

theorem digits_eq_mod {radix d : ℕ} (radixLarge : 1 < radix) (digits : Fin d → ℕ)
    (small : ∀ i, digits i < radix) (i : Fin d) :
    digits i = value radix digits / radix ^ i.val % radix := by
  have range := value_lt_pow radixLarge digits small
  have sameValue := value_mod_digits radix (value radix digits) d
  rw [Nat.div_eq_of_lt range, mul_zero, add_zero] at sameValue
  exact congrFun (digits_unique radixLarge digits _ small
    (fun _ => Nat.mod_lt _ (by omega)) sameValue.symm) i

theorem modulus_value (p radix d : ℕ) (enough : p - 1 < radix ^ d) :
    value radix (fun i : Fin d => modulusDigit p radix i.val) = p - 1 := by
  simpa only [modulusDigit, Nat.div_eq_of_lt enough, mul_zero, add_zero] using
    value_mod_digits radix (p - 1) d

def digitCount (p radix : ℕ) : ℕ := (Nat.digits radix (p - 1)).length

theorem digitCount_enough (p radix : ℕ) (radixLarge : 1 < radix) :
    p - 1 < radix ^ digitCount p radix :=
  Nat.lt_base_pow_length_digits radixLarge

theorem transition_bound {radix digit bound incoming : ℕ}
    (digitSmall : digit < radix) (bit : incoming ≤ 1) :
    digit + incoming ≤ bound + radix * (if bound < digit + incoming then 1 else 0) := by
  split_ifs <;> omega

def table (p radix bound : ℕ) : List (Fin 3 → ZMod p) :=
  (List.finRange radix).flatMap fun digit => (List.finRange 2).map fun incoming =>
    ![(digit.val : ZMod p), (incoming.val : ZMod p),
      ((if bound < digit.val + incoming.val then 1 else 0 : ℕ) : ZMod p)]

theorem mem_table_iff (p radix bound : ℕ) (row : Fin 3 → ZMod p) :
    row ∈ table p radix bound ↔ ∃ digit : Fin radix, ∃ incoming : Fin 2,
      row = ![(digit.val : ZMod p), (incoming.val : ZMod p),
        ((if bound < digit.val + incoming.val then 1 else 0 : ℕ) : ZMod p)] := by
  simp [table, List.mem_flatMap, eq_comm]

/-- Recover natural-number facts from the actual field-valued public table. -/
theorem table_values {p radix bound : ℕ} (radixLarge : 1 < radix) (radixSmall : radix < p)
    (digit incoming outgoing : ZMod p) (member : ![digit, incoming, outgoing] ∈ table p radix bound) :
    digit.val < radix ∧ incoming.val ≤ 1 ∧
      outgoing.val = if bound < digit.val + incoming.val then 1 else 0 := by
  obtain ⟨di, bi, equal⟩ := (mem_table_iff p radix bound _).mp member
  have hd := congrFun equal 0
  have hi := congrFun equal 1
  have ho := congrFun equal 2
  change digit = (di.val : ZMod p) at hd
  change incoming = (bi.val : ZMod p) at hi
  change outgoing = ((if bound < di.val + bi.val then 1 else 0 : ℕ) : ZMod p) at ho
  have dval : digit.val = di.val := by rw [hd, ZMod.val_natCast_of_lt (di.isLt.trans radixSmall)]
  have ival : incoming.val = bi.val := by rw [hi, ZMod.val_natCast_of_lt (by have := bi.isLt; omega)]
  refine ⟨by rw [dval]; exact di.isLt, by rw [ival]; have := bi.isLt; omega, ?_⟩
  rw [ho, ZMod.val_natCast_of_lt (by split_ifs <;> omega), dval, ival]

variable {p radix d b n : ℕ}

/-- This is membership in the literal public tables, at one active scalar
position. No membership condition on inactive padding is imposed here. -/
def LookupAt (p radix : ℕ) {d b n : ℕ}
    (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) : Prop :=
  ∀ i : Fin d,
    ![tables (DecompositionLinear.digit i) cell lane,
      tables (DecompositionLinear.borrow i.castSucc) cell lane,
      tables (DecompositionLinear.borrow i.succ) cell lane] ∈ table p radix (modulusDigit p radix i.val)

def CanonicalAt (p radix : ℕ) {d b n : ℕ}
    (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) : Prop :=
  value radix (fun i => (tables (DecompositionLinear.digit i) cell lane).val) =
    (tables DecompositionLinear.input cell lane).val

theorem integer_bound (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p - 1 < radix ^ d)
    (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) (lookup : LookupAt p radix tables cell lane)
    (first : tables DecompositionLinear.firstBorrow cell lane = 0)
    (last : tables DecompositionLinear.lastBorrow cell lane = 0) :
    value radix (fun i => (tables (DecompositionLinear.digit i) cell lane).val) < p := by
  have localStep (i : Fin d) :
      (tables (DecompositionLinear.digit i) cell lane).val +
        (tables (DecompositionLinear.borrow i.castSucc) cell lane).val ≤
      modulusDigit p radix i.val + radix * (tables (DecompositionLinear.borrow i.succ) cell lane).val := by
    have facts := table_values radixLarge radixSmall _ _ _ (lookup i)
    rw [facts.2.2]
    exact transition_bound facts.1 facts.2.1
  have bound := weighted_bound radix d
    (fun i => (tables (DecompositionLinear.digit i) cell lane).val)
    (fun i => modulusDigit p radix i.val)
    (fun i => (tables (DecompositionLinear.borrow i) cell lane).val) localStep
  have initial : (tables (DecompositionLinear.borrow (0 : Fin (d + 1))) cell lane).val = 0 := by
    change (tables DecompositionLinear.firstBorrow cell lane).val = 0
    rw [first]
    exact ZMod.val_zero
  have terminal : (tables (DecompositionLinear.borrow (Fin.last d)) cell lane).val = 0 := by
    change (tables DecompositionLinear.lastBorrow cell lane).val = 0
    rw [last]
    exact ZMod.val_zero
  rw [initial, terminal, add_zero, mul_zero, add_zero, modulus_value p radix d enough] at bound
  omega

variable [Fact p.Prime]

/-- Integer canonicity follows from the two actual semantic constraint
families. This theorem does not assume or supply lookup-verifier security. -/
theorem canonical_of_constraints
    (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p - 1 < radix ^ d)
    (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → ZMod p)
    (valid : DecompositionLinear.Relation (radix : ZMod p) tables)
    (cell : MatrixFold.Cube n) (lane : Fin b) (lookup : LookupAt p radix tables cell lane) :
    CanonicalAt p radix tables cell lane := by
  have range := integer_bound radixLarge radixSmall enough tables cell lane lookup
    (valid cell lane).2.1 (valid cell lane).2.2
  have equal : (value radix (fun i => (tables (DecompositionLinear.digit i) cell lane).val) : ZMod p) =
      tables DecompositionLinear.input cell lane := by
    rw [value, Nat.cast_sum]
    simp only [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
    exact (valid cell lane).1.symm
  have representatives := congrArg ZMod.val equal
  rwa [ZMod.val_natCast_of_lt range] at representatives

theorem canonical_of_digitCount
    (radixLarge : 1 < radix) (radixSmall : radix < p)
    (tables : Fin (2 * digitCount p radix + 2) → MatrixFold.Cube n → Fin b → ZMod p)
    (valid : DecompositionLinear.Relation (radix : ZMod p) tables)
    (cell : MatrixFold.Cube n) (lane : Fin b) (lookup : LookupAt p radix tables cell lane) :
    CanonicalAt p radix tables cell lane :=
  canonical_of_constraints radixLarge radixSmall (digitCount_enough p radix radixLarge) tables valid cell lane lookup

/-- Each authenticated digit has the actual base-radix quotient/remainder
value, not merely a field-congruent reconstruction. -/
theorem digits_of_constraints
    (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p - 1 < radix ^ d)
    (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → ZMod p)
    (valid : DecompositionLinear.Relation (radix : ZMod p) tables)
    (cell : MatrixFold.Cube n) (lane : Fin b) (lookup : LookupAt p radix tables cell lane) (i : Fin d) :
    (tables (DecompositionLinear.digit i) cell lane).val =
      (tables DecompositionLinear.input cell lane).val / radix ^ i.val % radix := by
  have canonical := canonical_of_constraints radixLarge radixSmall enough tables valid cell lane lookup
  change value radix (fun i => (tables (DecompositionLinear.digit i) cell lane).val) =
    (tables DecompositionLinear.input cell lane).val at canonical
  have extracted := digits_eq_mod radixLarge
    (fun i => (tables (DecompositionLinear.digit i) cell lane).val)
    (fun i => (table_values radixLarge radixSmall _ _ _ (lookup i)).1) i
  simpa only [canonical] using extracted

/-- A noncanonical active position violates the authenticated linear relation
or at least one concrete public-table lookup. No lookup error is discarded. -/
theorem failure_dichotomy
    (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p - 1 < radix ^ d)
    (tables : Fin (2 * d + 2) → MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) (bad : ¬CanonicalAt p radix tables cell lane) :
    ¬DecompositionLinear.Relation (radix : ZMod p) tables ∨ ∃ i : Fin d,
      ![tables (DecompositionLinear.digit i) cell lane,
        tables (DecompositionLinear.borrow i.castSucc) cell lane,
        tables (DecompositionLinear.borrow i.succ) cell lane] ∉ table p radix (modulusDigit p radix i.val) := by
  classical
  by_cases valid : DecompositionLinear.Relation (radix : ZMod p) tables
  · right
    have failed : ¬LookupAt p radix tables cell lane :=
      fun lookup => bad (canonical_of_constraints radixLarge radixSmall enough tables valid cell lane lookup)
    exact not_forall.mp failed
  · exact Or.inl valid

end

end FormalProof4FHE.HasteBoots.RadixCanonicity
