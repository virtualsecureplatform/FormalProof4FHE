module

public import FormalProof4FHE.HasteBoots.NativeInterpolationField
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-!
# Safety of the literal scalar interpolation loop

The scan retains the actual consecutive-node differences. An off-node result
therefore certifies nonzero differences. With the validated noncolliding-node
range, the descending loop's factorial accumulator and every division remain
nonzero. These are properties of the literal loop, not caller certificates.
-/

namespace FormalProof4FHE.HasteBoots.NativeInterpolationSafety

open NativeInterpolationCore NativeInterpolationField

noncomputable section

variable {K : Type} [Field K]

/-- Mathematical description of the scan's actual retained prefix. -/
def nodeState (point : K) (index : ℕ) : ScanState K :=
  let differences := (List.range (index + 1)).map (fun (j : ℕ) => point - (j : K))
  ⟨(index : K), differences.prod, differences⟩

theorem nodeState_zero (point : K) : nodeState point 0 = ⟨0, point, [point]⟩ := by
  simp [nodeState]

theorem extend_nodeState (point : K) (index : ℕ) :
    extend (arithmetic K) point (nodeState point index) = nodeState point (index + 1) := by
  simp only [extend, arithmetic, nodeState, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, Nat.cast_add, Nat.cast_one]

theorem scan_nodes (point : K) (remaining index : ℕ) :
    match scan (arithmetic K) point remaining index (nodeState point index) with
    | .atNode found => point = (found : K)
    | .offNodes state => state = nodeState point (index + remaining) ∧
        ∀ j, index ≤ j → j ≤ index + remaining → point ≠ (j : K) := by
  induction remaining generalizing index with
  | zero =>
    by_cases matched : point = (index : K)
    · rw [scan_equal (arithmetic K) point 0 index _ (by simpa [arithmetic, nodeState] using matched)]
      exact matched
    · rw [scan, ite_eq_right (by simpa [arithmetic, nodeState] using matched)]
      refine ⟨by simp, ?_⟩
      intro j lower upper
      have same : j = index := by omega
      simpa only [same] using matched
  | succ remaining ih =>
    by_cases matched : point = (index : K)
    · rw [scan_equal (arithmetic K) point (remaining + 1) index _ (by simpa [arithmetic, nodeState] using matched)]
      exact matched
    · rw [scan, ite_eq_right (by simpa [arithmetic, nodeState] using matched), extend_nodeState]
      have next := ih (index + 1)
      cases finished : scan (arithmetic K) point remaining (index + 1) (nodeState point (index + 1)) with
      | atNode found => simpa only [finished] using next
      | offNodes state =>
        rw [finished] at next
        refine ⟨?_, ?_⟩
        · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next.1
        · intro j lower upper
          by_cases first : j = index
          · simpa only [first] using matched
          · exact next.2 j (by omega) (by omega)

/-- An off-node scan rules out every zero denominator difference. -/
theorem offNodes_nonzero (point : K) (degree : ℕ) (state : ScanState K)
    (finished : scan (arithmetic K) point degree 0 ⟨0, point, [point]⟩ = .offNodes state) :
    state = nodeState point degree ∧ ∀ value ∈ state.differences, value ≠ 0 := by
  have scanned := scan_nodes point degree 0
  rw [nodeState_zero, finished] at scanned
  simp only [Nat.zero_add] at scanned
  refine ⟨scanned.1, ?_⟩
  rw [scanned.1]
  intro value member
  rcases List.mem_map.mp member with ⟨j, inRange, rfl⟩
  apply sub_ne_zero.mpr
  exact scanned.2 j (Nat.zero_le _) (by have bound := List.mem_range.mp inRange; omega)

/-- The native node preflight implies a nonzero initial factorial. -/
theorem factorial_nonzero (degree : ℕ)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) : (degree.factorial : K) ≠ 0 := by
  induction degree with
  | zero => simp
  | succ degree ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    exact mul_ne_zero (nodes (degree + 1) (by omega) (by omega))
      (ih (fun j positive small => nodes j positive (by omega)))

/-- Checked accesses and every native division succeed in the descending loop.
The counter relation is maintained by the actual nonfinal update. -/
theorem reverse_safe (values differences : List K) (product : K) (degree count step : ℕ)
    (state : ReverseState K)
    (valueBound : count ≤ values.length) (differenceBound : count ≤ differences.length)
    (nonzero : ∀ value ∈ differences, value ≠ 0)
    (counter : state.remainingField = ((step + 1 : ℕ) : K)) (up : state.up ≠ 0)
    (remaining : count + step = degree + 1)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) :
    ∃ final, reverse (arithmetic K) values differences product count state = some final := by
  induction count generalizing step state with
  | zero => exact ⟨state, rfl⟩
  | succ index ih =>
    have valueIndex : index < values.length := by omega
    have differenceIndex : index < differences.length := by omega
    have denominator : state.up * differences[index] ≠ 0 :=
      mul_ne_zero up (nonzero _ (List.getElem_mem differenceIndex))
    let term := (values[index] * product * state.down) / (state.up * differences[index])
    have division : (arithmetic K).divide
        ((arithmetic K).mul ((arithmetic K).mul values[index] product) state.down)
        ((arithmetic K).mul state.up differences[index]) = some term := by
      simp only [arithmetic, denominator, ite_false]
      rfl
    simp only [reverse, List.getElem?_eq_getElem valueIndex,
      List.getElem?_eq_getElem differenceIndex, Option.bind_some, division]
    by_cases final : index = 0
    · rw [ite_eq_left final]
      exact ⟨_, rfl⟩
    · rw [ite_eq_right final]
      apply ih (step + 1) (advance (arithmetic K) term state) (by omega) (by omega)
      · simp only [advance, arithmetic, counter, Nat.cast_add, Nat.cast_one]
      · change state.up * -state.remainingField ≠ 0
        rw [counter]
        exact mul_ne_zero up (neg_ne_zero.mpr (nodes (step + 1) (by omega) (by omega)))
      · omega

/-- The validated node range makes interpolation total for every challenge.
No denominator or successful execution certificate is an additional premise. -/
theorem interpolate_safe (values : List K) (point : K) (positive : 0 < values.length)
    (nodes : ∀ j, 0 < j → j ≤ values.length - 1 → (j : K) ≠ 0) :
    ∃ value, interpolate (arithmetic K) values point = some value := by
  cases values with
  | nil => simp at positive
  | cons first rest =>
    have valid : ∀ j, 0 < j → j ≤ rest.length → (j : K) ≠ 0 := by
      simpa only [List.length_cons, Nat.add_sub_cancel] using nodes
    simp only [interpolate, List.length_cons, Nat.add_sub_cancel,
      show (arithmetic K).zero = (0 : K) from rfl, show (arithmetic K).one = (1 : K) from rfl]
    cases finished : scan (arithmetic K) point rest.length 0 ⟨0, point, [point]⟩ with
    | atNode index =>
      have bound := scan_bounds (arithmetic K) point rest.length 0 ⟨0, point, [point]⟩
      rw [finished] at bound
      have inRange : index < (first :: rest).length := by simp only [List.length_cons]; omega
      exact ⟨(first :: rest)[index], List.getElem?_eq_getElem inRange⟩
    | offNodes scanned =>
      have nonzero := (offNodes_nonzero point rest.length scanned finished).2
      have width := offNodes_length (arithmetic K) (first :: rest) point (by simp) scanned
        (by
          change scan (arithmetic K) point rest.length 0 ⟨0, point, [point]⟩ = .offNodes scanned
          exact finished)
      let initial : ReverseState K := ⟨0, (factorial (arithmetic K) rest.length).1, 1, scanned.check, 1⟩
      have up : initial.up ≠ 0 := by
        change (factorial (arithmetic K) rest.length).1 ≠ 0
        rw [NativeInterpolationField.factorial_value]
        exact factorial_nonzero rest.length valid
      obtain ⟨final, success⟩ := reverse_safe (first :: rest) scanned.differences scanned.product
        rest.length (rest.length + 1) 0 initial (by simp) (by simpa only [List.length_cons] using width.ge)
        nonzero (by simp only [initial, Nat.zero_add, Nat.cast_one]) up (by omega) valid
      refine ⟨final.result, ?_⟩
      change (reverse (arithmetic K) (first :: rest) scanned.differences scanned.product
        (rest.length + 1) initial).map ReverseState.result = some final.result
      rw [success, Option.map_some]

/-- The literal preflight's nonzero casts make all consecutive nodes distinct. -/
theorem nodes_injective (degree : ℕ)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) :
    Function.Injective (fun node : Fin (degree + 1) => (node.val : K)) := by
  intro first second equal
  change (first.val : K) = (second.val : K) at equal
  apply Fin.ext
  by_contra different
  by_cases order : first.val ≤ second.val
  · have nonzero := nodes (second.val - first.val) (by omega) (by have bound := second.isLt; omega)
    apply nonzero
    rw [Nat.cast_sub order, ← equal, sub_self]
  · have nonzero := nodes (first.val - second.val) (by omega) (by have bound := first.isLt; omega)
    apply nonzero
    rw [Nat.cast_sub (by omega : second.val ≤ first.val), equal, sub_self]

/-- At every validated node, the actual scan takes the matching early return. -/
theorem scan_at_node (degree : ℕ)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) (node : Fin (degree + 1)) :
    scan (arithmetic K) (node.val : K) degree 0 ⟨0, (node.val : K), [(node.val : K)]⟩ = .atNode node.val := by
  have spec := scan_nodes (node.val : K) degree 0
  rw [nodeState_zero] at spec
  cases finished : scan (arithmetic K) (node.val : K) degree 0 ⟨0, (node.val : K), [(node.val : K)]⟩ with
  | atNode found =>
    rw [finished] at spec
    have bounds := scan_bounds (arithmetic K) (node.val : K) degree 0 ⟨0, (node.val : K), [(node.val : K)]⟩
    rw [finished] at bounds
    have inside : found < degree + 1 := by omega
    have same := nodes_injective degree nodes (show (node.val : K) = ((⟨found, inside⟩ : Fin (degree + 1)).val : K) from spec)
    exact congrArg ScanResult.atNode (congrArg Fin.val same).symm
  | offNodes state =>
    rw [finished] at spec
    exact False.elim (spec.2 node.val (Nat.zero_le _) (by have bound := node.isLt; omega) rfl)

/-- Known-node interpolation returns the received evaluation exactly. -/
theorem interpolate_at_node (values : List K) (positive : 0 < values.length)
    (nodes : ∀ j, 0 < j → j ≤ values.length - 1 → (j : K) ≠ 0) (node : Fin values.length) :
    interpolate (arithmetic K) values (node.val : K) = some values[node.val] := by
  cases values with
  | nil => simp at positive
  | cons first rest =>
    have valid : ∀ j, 0 < j → j ≤ rest.length → (j : K) ≠ 0 := by
      simpa only [List.length_cons, Nat.add_sub_cancel] using nodes
    have index : node.val < rest.length + 1 := by simpa only [List.length_cons] using node.isLt
    have matched := scan_at_node rest.length valid ⟨node.val, index⟩
    simp only [interpolate, List.length_cons, Nat.add_sub_cancel,
      show (arithmetic K).zero = (0 : K) from rfl]
    rw [matched]
    exact List.getElem?_eq_getElem node.isLt

end

end FormalProof4FHE.HasteBoots.NativeInterpolationSafety
