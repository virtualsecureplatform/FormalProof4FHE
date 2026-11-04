module

public import FormalProof4FHE.HasteBoots.NativeTerminalCore
public import FormalProof4FHE.HasteBoots.NativeInterpolationField
public import FormalProof4FHE.HasteBoots.ExtensionLookupIdentity

@[expose] public section

/-!
# Field meaning of the literal lookup terminal loops

The unsigned shift-and-mask loop is identified with the already proved
active-prefix MLE, with every original point coordinate retained. Equality
uses exactly the native zip/fold and the validated equal-dimension inputs.
-/

namespace FormalProof4FHE.HasteBoots.NativeTerminalField

open NativeInterpolationField NativeTerminalCore
open NativeUsizeMessage (Usize)
open scoped BigOperators

noncomputable section

variable {K : Type} [Field K]

theorem equalityFrom_value (pairs : List (K × K)) (out : K) :
    equalityFrom (arithmetic K) pairs out =
      out * (pairs.map (fun pair => pair.1 * pair.2 + (1 - pair.1) * (1 - pair.2))).prod := by
  induction pairs generalizing out with
  | nil => simp only [equalityFrom, List.map_nil, List.prod_nil, mul_one]
  | cons pair rest ih =>
    rw [equalityFrom, ih]
    simp only [arithmetic, List.map_cons, List.prod_cons, mul_assoc]

omit [Field K] in
private theorem zip_ofFn {n : ℕ} (first second : Fin n → K) :
    (List.ofFn first).zip (List.ofFn second) = List.ofFn (fun i => (first i, second i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, List.zip_cons_cons]
    rw [ih]

theorem equality_value {n : ℕ} (first second : Fin n → K) :
    equality (arithmetic K) (List.ofFn first) (List.ofFn second) = ExtensionLookupIdentity.equality first second := by
  rw [equality, equalityFrom_value]
  simp only [arithmetic, one_mul, zip_ofFn, List.map_ofFn, Fin.prod_ofFn, ExtensionLookupIdentity.equality]
  rfl

/-- Every descending access uses its original coordinate, and every tested
bit is the actual machine threshold bit. -/
theorem prefixLoop_value (point : List K) (count : Usize) (remaining : ℕ)
    (threshold : PackedZeroEquality.Cell remaining) (values : Fin remaining → K)
    (inside : remaining ≤ point.length)
    (coordinates : ∀ i : Fin remaining, point[i.val]'(i.isLt.trans_le inside) = values i)
    (bits : ∀ i : Fin remaining, NativeTerminalBits.bit count i.val = finTwoEquiv (threshold i))
    (state : PrefixState K) :
    (prefixLoop (arithmetic K) point count remaining state).map PrefixState.out =
      some (NativePrefixMask.loop remaining threshold values state.same state.out) := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    have index : remaining < point.length := by omega
    have coordinate := coordinates (Fin.last remaining)
    have selected := bits (Fin.last remaining)
    simp only [Fin.val_last] at coordinate selected
    rw [prefixLoop, List.getElem?_eq_getElem index, Option.bind_some, coordinate]
    have lowCoordinates (i : Fin remaining) : point[i.val]'(by omega) = values i.castSucc := coordinates i.castSucc
    have lowBits (i : Fin remaining) : NativeTerminalBits.bit count i.val = finTwoEquiv (threshold i.castSucc) := bits i.castSucc
    by_cases highZero : threshold (Fin.last remaining) = 0
    · have high : NativeTerminalBits.bit count remaining = false := by rw [selected, highZero]; rfl
      simp only [prefixStep, high, Bool.false_eq_true, ite_false, arithmetic,
        NativePrefixMask.loop, highZero, ite_true]
      exact ih (fun i => threshold i.castSucc) (fun i => values i.castSucc) (by omega) lowCoordinates lowBits _
    · have highOne := Fin.eq_one_of_ne_zero _ highZero
      have high : NativeTerminalBits.bit count remaining = true := by rw [selected, highOne]; rfl
      simp only [prefixStep, high, ite_true, arithmetic, NativePrefixMask.loop, highZero, ite_false]
      exact ih (fun i => threshold i.castSucc) (fun i => values i.castSucc) (by omega) lowCoordinates lowBits _

/-- The full machine-domain prefix evaluator is the semantic active-prefix
mask, including empty points, count zero, and the full-table shortcut. -/
theorem prefixValue_value {n : ℕ} (point : Fin n → K) (count : Usize)
    (shift : n < 64) (enough : count.val ≤ 2 ^ n) :
    prefixValue (arithmetic K) (List.ofFn point) count =
      some (NativePrefixMask.evaluatePrefix point count.val enough) := by
  rw [prefixValue, List.length_ofFn, ite_eq_left shift, NativePrefixMask.evaluatePrefix]
  by_cases full : count.val = 2 ^ n
  · rw [ite_eq_left full, dite_eq_left full]
    rfl
  · rw [ite_eq_right full, dite_eq_right full]
    let threshold := (NativeEqualityTable.address n).symm ⟨count.val, by omega⟩
    have result := prefixLoop_value (List.ofFn point) count n threshold point (by simp)
      (fun i => by simp only [List.getElem_ofFn])
      (fun i => NativeTerminalBits.threshold_bit n count (by omega) i) ⟨1, 0⟩
    exact result

end

end FormalProof4FHE.HasteBoots.NativeTerminalField
