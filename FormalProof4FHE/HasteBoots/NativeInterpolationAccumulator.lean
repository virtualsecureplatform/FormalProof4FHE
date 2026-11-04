module

public import FormalProof4FHE.HasteBoots.NativeInterpolationWeights

@[expose] public section

/-!
# Result of the literal descending interpolation accumulator

The proof retains both native denominator accumulators and their exact
updates. Its invariant identifies their ratio with the consecutive-node
Lagrange denominator; the loop returns the resulting finite partial sum.
-/

namespace FormalProof4FHE.HasteBoots.NativeInterpolationAccumulator

open NativeInterpolationCore NativeInterpolationField NativeInterpolationSafety NativeInterpolationWeights
open scoped BigOperators

noncomputable section

variable {K : Type} [Field K]

def partialSum (degree : ℕ) (values : List K) (point product : K) (count : ℕ)
    (inside : count ≤ values.length) : K :=
  ∑ index : Fin count, values[index.val]'(index.isLt.trans_le inside) * product /
    (denominator degree index.val * (point - (index.val : K)))

theorem partialSum_succ (degree : ℕ) (values : List K) (point product : K) (count : ℕ)
    (inside : count + 1 ≤ values.length) :
    partialSum degree values point product (count + 1) inside =
      partialSum degree values point product count (by omega) +
      values[count]'(by omega) * product / (denominator degree count * (point - (count : K))) := by
  rw [partialSum, Fin.sum_univ_castSucc]
  rfl

theorem difference_value (point : K) (degree index : ℕ) (inside : index < degree + 1) :
    (nodeState point degree).differences[index]'(by simp only [nodeState, List.length_map, List.length_range]; omega) =
      point - (index : K) := by
  simp only [nodeState, List.getElem_map, List.getElem_range]

/-- The exact reverse-loop update preserves the denominator ratio. -/
theorem advance_ratio (degree index : ℕ) (positive : 0 < index) (inside : index ≤ degree)
    (term : K) (state : ReverseState K)
    (ratio : state.up = state.down * denominator degree index)
    (counter : state.remainingField = ((degree - index + 1 : ℕ) : K))
    (position : state.indexField = (index : K)) :
    (advance (arithmetic K) term state).up =
      (advance (arithmetic K) term state).down * denominator degree (index - 1) := by
  have adjacent := denominator_step (K := K) degree (index - 1) (by omega)
  have previous : index - 1 + 1 = index := by omega
  have distance : degree - (index - 1) = degree - index + 1 := by omega
  rw [previous, distance] at adjacent
  change state.up * -state.remainingField = (state.down * state.indexField) * denominator degree (index - 1)
  rw [ratio, counter, position]
  calc
    _ = state.down * (-((degree - index + 1 : ℕ) : K) * denominator degree index) := by ring
    _ = _ := by rw [← adjacent]; ring

/-- Every processed term is exactly its barycentric summand. The `down`
accumulator cancels algebraically, while remaining in the literal execution. -/
theorem term_value (degree index : ℕ) (value point product : K) (state : ReverseState K)
    (ratio : state.up = state.down * denominator degree index) (down : state.down ≠ 0) :
    (value * product * state.down) / (state.up * (point - (index : K))) =
      value * product / (denominator degree index * (point - (index : K))) := by
  rw [ratio]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (mul_div_mul_right (value * product) (denominator degree index * (point - (index : K))) down)

/-- The actual descending loop computes the complete sum of its processed
barycentric terms, for arbitrary positive remaining count. -/
theorem reverse_value (degree : ℕ) (values : List K) (point product : K) (count : ℕ)
    (state : ReverseState K) (positive : 0 < count)
    (width : count ≤ values.length) (inside : count ≤ degree + 1)
    (position : state.indexField = ((count - 1 : ℕ) : K))
    (counter : state.remainingField = ((degree - (count - 1) + 1 : ℕ) : K))
    (ratio : state.up = state.down * denominator degree (count - 1)) (down : state.down ≠ 0)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0)
    (offNodes : ∀ j, j ≤ degree → point ≠ (j : K)) :
    (reverse (arithmetic K) values (nodeState point degree).differences product count state).map ReverseState.result =
      some (state.result + partialSum degree values point product count width) := by
  induction count generalizing state with
  | zero => omega
  | succ index ih =>
    have valueIndex : index < values.length := by omega
    have indexBound : index ≤ degree := by omega
    have differenceIndex : index < (nodeState point degree).differences.length := by
      simp only [nodeState, List.length_map, List.length_range]
      omega
    have ratioNow : state.up = state.down * denominator degree index := by
      simpa only [Nat.add_sub_cancel] using ratio
    have denominatorNonzero : state.up * (nodeState point degree).differences[index] ≠ 0 := by
      rw [ratioNow, difference_value point degree index (by omega)]
      exact mul_ne_zero (mul_ne_zero down (denominator_nonzero degree index indexBound nodes))
        (sub_ne_zero.mpr (offNodes index indexBound))
    let term := values[index] * product / (denominator degree index * (point - (index : K)))
    have division : (arithmetic K).divide
        ((arithmetic K).mul ((arithmetic K).mul values[index] product) state.down)
        ((arithmetic K).mul state.up (nodeState point degree).differences[index]) = some term := by
      simp only [arithmetic, denominatorNonzero, ite_false]
      rw [difference_value point degree index (by omega)]
      exact congrArg some (term_value degree index values[index] point product state ratioNow down)
    simp only [reverse, List.getElem?_eq_getElem valueIndex,
      List.getElem?_eq_getElem differenceIndex, Option.bind_some, division]
    by_cases final : index = 0
    · subst index
      simp only [ite_true, Option.map_some]
      change some (state.result + term) = some (state.result + partialSum degree values point product 1 width)
      rw [partialSum_succ]
      simp only [partialSum, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
      rfl
    · rw [ite_eq_right final]
      have positiveIndex : 0 < index := by omega
      have nextPosition : (advance (arithmetic K) term state).indexField = ((index - 1 : ℕ) : K) := by
        change state.indexField - 1 = _
        rw [position, Nat.add_sub_cancel, Nat.cast_sub (by omega : 1 ≤ index), Nat.cast_one]
      have nextCounter : (advance (arithmetic K) term state).remainingField =
          ((degree - (index - 1) + 1 : ℕ) : K) := by
        change state.remainingField + 1 = _
        rw [counter, Nat.add_sub_cancel]
        have difference : degree - (index - 1) + 1 = (degree - index + 1) + 1 := by omega
        simp only [difference, Nat.cast_add, Nat.cast_one]
      have nextRatio := advance_ratio degree index positiveIndex indexBound term state ratioNow
        (by simpa only [Nat.add_sub_cancel] using counter) (by simpa only [Nat.add_sub_cancel] using position)
      have nextDown : (advance (arithmetic K) term state).down ≠ 0 := by
        change state.down * state.indexField ≠ 0
        rw [position, Nat.add_sub_cancel]
        exact mul_ne_zero down (nodes index positiveIndex indexBound)
      rw [ih (advance (arithmetic K) term state) positiveIndex (by omega) (by omega)
        nextPosition nextCounter nextRatio nextDown]
      rw [partialSum_succ]
      change some ((state.result + term) + partialSum degree values point product index _) =
        some (state.result + (partialSum degree values point product index _ + term))
      congr 1
      ring

end

end FormalProof4FHE.HasteBoots.NativeInterpolationAccumulator
