module
public import FormalProof4FHE.HasteBoots.AccumulatorShiftQueries
public import FormalProof4FHE.HasteBoots.MonomialBitOrder
@[expose] public section

/-! Complete coefficient/round/half queries for packed accumulator sources.
The coefficient prefix and half suffix remain fixed while only the row block
is transformed. These are exact matrix identities, not native acceptance. -/
namespace FormalProof4FHE.HasteBoots.AccumulatorPackedQueries
open scoped BigOperators
open Matrix
open PackedSumcheckSubclaim (Query)
noncomputable section
variable {F : Type} [Field F] {k c r s : ℕ}

/-- Earlier variables occupy the low address bits. -/
def append : {front back : ℕ} → Query F k front → Query F k back → Query F k (back+front)
  | _, _, .nil, last => last
  | _, _, .cons pair tail, last => .cons pair (append tail last)

omit [Field F] in
theorem append_toList (front : Query F k c) (back : Query F k r) :
    (append front back).toList = front.toList++back.toList := by
  induction front with
  | nil => rfl
  | cons pair tail ih => simp only [append, Query.toList, ih, List.cons_append]

theorem fold_append (front : Query F k c) (back : Query F k r)
    (table : MatrixFold.Cube (r+c) → Fin k → F) :
    (append front back).fold table = back.fold (fun right => front.fold
      (fun left => table (MonomialBitOrder.append left right))) := by
  induction front with
  | nil => rfl
  | cons pair tail ih =>
    change (append tail back).fold (MatrixFold.foldFirst pair table) = _
    rw [ih]
    apply congrArg back.fold
    funext right
    apply congrArg tail.fold
    funext left
    rfl

def whole (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) : Query F k ((1+r)+c) :=
  append coefficient (append rows (.cons half .nil))

def coordinate (coefficient : MatrixFold.Cube c) (row : MatrixFold.Cube r) (half : Bool) :
    MatrixFold.Cube ((1+r)+c) :=
  MonomialBitOrder.append coefficient (MonomialBitOrder.append row (half,()))

omit [Field F] in
theorem whole_toList (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) :
    (whole coefficient rows half).toList = coefficient.toList++(rows.toList++[half]) := by
  simp only [whole, append_toList, Query.toList]

theorem coordinate_index (coefficient : MatrixFold.Cube c) (row : MatrixFold.Cube r) (half : Bool) :
    (FlatMatrixFold.index ((1+r)+c) (coordinate coefficient row half)).val =
      (FlatMatrixFold.index c coefficient).val+2^c*((FlatMatrixFold.index r row).val+2^r*(if half then 1 else 0)) := by
  have origin : (FlatMatrixFold.index 0 ()).val = 0 := by
    have := (FlatMatrixFold.index 0 ()).isLt
    change _ < 1 at this
    omega
  unfold coordinate
  rw [MonomialBitOrder.flat_append coefficient (MonomialBitOrder.append row (show MatrixFold.Cube 1 from (half,())))]
  rw [MonomialBitOrder.flat_append row (show MatrixFold.Cube 1 from (half,()))]
  rw [FlatMatrixFold.index_succ_val (n := 0) half (), origin]
  simp only [Nat.mul_zero, Nat.zero_add]

theorem whole_fold (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (table : MatrixFold.Cube ((1+r)+c) → Fin k → F) :
    (whole coefficient rows half).fold table =
      half false *ᵥ rows.fold (fun row => coefficient.fold (fun cell => table (coordinate cell row false))) +
      half true *ᵥ rows.fold (fun row => coefficient.fold (fun cell => table (coordinate cell row true))) := by
  simp only [whole, fold_append, Query.fold, MatrixFold.foldFirst, Fintype.sum_bool]
  exact add_comm _ _

/-- Linearity in the source, without changing the query or any matrix order. -/
theorem fold_add (query : Query F k s) (first last : MatrixFold.Cube s → Fin k → F) :
    query.fold (fun cell => first cell+last cell) = query.fold first+query.fold last := by
  simp only [AccumulatorShiftQueries.fold_eq_weighted, Matrix.mulVec_add, Finset.sum_add_distrib]

theorem fold_sub (query : Query F k s) (first last : MatrixFold.Cube s → Fin k → F) :
    query.fold (fun cell => first cell-last cell) = query.fold first-query.fold last := by
  simp only [AccumulatorShiftQueries.fold_eq_weighted, Matrix.mulVec_sub, Finset.sum_sub_distrib]

theorem fold_zero (query : Query F k s) : query.fold (fun _ => (0 : Fin k → F)) = 0 := by
  simp only [AccumulatorShiftQueries.fold_eq_weighted, Matrix.mulVec_zero, Finset.sum_const_zero]

theorem sum_mix {α : Type} (entries : List α) (left right : α → Fin k → F)
    (a b : Matrix (Fin k) (Fin k) F) :
    (entries.map (fun entry => a *ᵥ left entry+b *ᵥ right entry)).sum =
      a *ᵥ (entries.map left).sum+b *ᵥ (entries.map right).sum := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, Matrix.mulVec_add]
    abel

def shiftWhole (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) : List (Query F k ((1+r)+c)) :=
  (AccumulatorShiftQueries.shifted rows).map (fun branch => whole coefficient branch half)

theorem shiftWhole_toList (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) :
    (shiftWhole coefficient rows half).map Query.toList =
      (AccumulatorShiftQueries.shifted rows).map (fun branch => coefficient.toList++(branch.toList++[half])) := by
  simp only [shiftWhole, List.map_map, Function.comp_def, whole_toList]

/-- Every branch opens the same complete source with the same outer blocks. -/
theorem shiftWhole_fold (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (table : MatrixFold.Cube ((1+r)+c) → Fin k → F) :
    ((shiftWhole coefficient rows half).map (fun branch => branch.fold table)).sum =
      half false *ᵥ rows.fold (fun row => coefficient.fold (fun cell => table (coordinate cell (AccumulatorShiftQueries.successor row) false))) +
      half true *ᵥ rows.fold (fun row => coefficient.fold (fun cell => table (coordinate cell (AccumulatorShiftQueries.successor row) true))) := by
  simp only [shiftWhole, List.map_map, Function.comp_def, whole_fold]
  rw [sum_mix, AccumulatorShiftQueries.shifted_fold, AccumulatorShiftQueries.shifted_fold]

theorem selectWhole_fold (coefficient : Query F k c) (target : MatrixFold.Cube r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (table : MatrixFold.Cube ((1+r)+c) → Fin k → F) :
    (whole coefficient (AccumulatorShiftQueries.selected target) half).fold table =
      half false *ᵥ coefficient.fold (fun cell => table (coordinate cell target false)) +
      half true *ᵥ coefficient.fold (fun cell => table (coordinate cell target true)) := by
  rw [whole_fold, AccumulatorShiftQueries.selected_fold, AccumulatorShiftQueries.selected_fold]

/-- Native duplicated-half query: retain the sum of the two original matrices. -/
def selectHalf (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (target : Bool) :
    MatrixFold.Pair (F := F) (Lane := Fin k) :=
  AccumulatorShiftQueries.selector target (half false+half true)

theorem selectHalf_fold (coefficient : Query F k c) (rows : Query F k r) (target : Bool)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (table : MatrixFold.Cube ((1+r)+c) → Fin k → F) :
    (whole coefficient rows (selectHalf half target)).fold table =
      (half false+half true) *ᵥ rows.fold (fun row => coefficient.fold (fun cell => table (coordinate cell row target))) := by
  rw [whole_fold]
  cases target <;> simp [selectHalf, AccumulatorShiftQueries.selector]

theorem duplicate_fold (coefficient : Query F k c) (rows : Query F k r) (target : Bool)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k))
    (input duplicate : MatrixFold.Cube ((1+r)+c) → Fin k → F)
    (copies : ∀ cell row choice, duplicate (coordinate cell row choice) = input (coordinate cell row target)) :
    (whole coefficient rows (selectHalf half target)).fold input = (whole coefficient rows half).fold duplicate := by
  rw [selectHalf_fold, whole_fold, Matrix.add_mulVec]
  have same (choice : Bool) : rows.fold (fun row => coefficient.fold (fun cell => duplicate (coordinate cell row choice))) =
      rows.fold (fun row => coefficient.fold (fun cell => input (coordinate cell row target))) := by
    apply congrArg rows.fold
    funext row
    apply congrArg coefficient.fold
    funext cell
    exact copies cell row choice
  rw [same false, same true]

/-- A fixed row basis vector, addressed by the same finite native row index. -/
def impulse (target : MatrixFold.Cube r) (value : Fin k → F) (row : MatrixFold.Cube r) : Fin k → F :=
  if FlatMatrixFold.index r row = FlatMatrixFold.index r target then value else 0

theorem fold_impulse (rows : Query F k r) (target : MatrixFold.Cube r) (value : Fin k → F) :
    rows.fold (impulse target value) = AccumulatorShiftQueries.weight rows target *ᵥ value := by
  classical
  rw [AccumulatorShiftQueries.fold_eq_weighted, Finset.sum_eq_single target]
  · simp only [impulse, ite_true]
  · intro row _ different
    have unequal : FlatMatrixFold.index r row ≠ FlatMatrixFold.index r target :=
      fun same => different ((FlatMatrixFold.index r).injective same)
    simp only [impulse, ite_eq_right unequal, Matrix.mulVec_zero]
  · simp

theorem coefficient_impulse (coefficient : Query F k c) (target row : MatrixFold.Cube r)
    (endpoint : MatrixFold.Cube c → Fin k → F) :
    coefficient.fold (fun cell => impulse target (endpoint cell) row) = impulse target (coefficient.fold endpoint) row := by
  by_cases equal : FlatMatrixFold.index r row = FlatMatrixFold.index r target
  · simp only [impulse, ite_eq_left equal]
  · simp only [impulse, ite_eq_right equal]
    exact fold_zero coefficient

/-- Endpoint corrections are row weights followed by the original half
matrices, exactly the order in row_weight/mix_halves. -/
theorem whole_impulse (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (target : MatrixFold.Cube r)
    (endpoint : Bool → MatrixFold.Cube c → Fin k → F)
    (table : MatrixFold.Cube ((1+r)+c) → Fin k → F)
    (pointmass : ∀ cell row choice, table (coordinate cell row choice) = impulse target (endpoint choice cell) row) :
    (whole coefficient rows half).fold table =
      half false *ᵥ (AccumulatorShiftQueries.weight rows target *ᵥ coefficient.fold (endpoint false)) +
      half true *ᵥ (AccumulatorShiftQueries.weight rows target *ᵥ coefficient.fold (endpoint true)) := by
  rw [whole_fold]
  have folded (choice : Bool) : rows.fold (fun row => coefficient.fold (fun cell => table (coordinate cell row choice))) =
      AccumulatorShiftQueries.weight rows target *ᵥ coefficient.fold (endpoint choice) := by
    have inside : (fun row => coefficient.fold (fun cell => table (coordinate cell row choice))) =
        impulse target (coefficient.fold (endpoint choice)) := by
      funext row
      have same : coefficient.fold (fun cell => table (coordinate cell row choice)) =
          coefficient.fold (fun cell => impulse target (endpoint choice cell) row) := by
        apply congrArg coefficient.fold
        funext cell
        exact pointmass cell row choice
      exact same.trans (coefficient_impulse coefficient target row (endpoint choice))
    rw [inside]
    exact fold_impulse rows target _
  rw [folded false, folded true]

/-- Native mix_halves after coefficient evaluation and ordered row weighting. -/
def correction (coefficient : Query F k c) (half : MatrixFold.Pair (F := F) (Lane := Fin k))
    (weight : Matrix (Fin k) (Fin k) F) (endpoint : Bool → MatrixFold.Cube c → Fin k → F) : Fin k → F :=
  half false *ᵥ (weight *ᵥ coefficient.fold (endpoint false)) +
    half true *ᵥ (weight *ᵥ coefficient.fold (endpoint true))

/-- The complete shifted-input equation, with both native endpoint correction
terms, follows from its pointwise coefficient/round/half constraint. -/
theorem continuity_check (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (start finish : MatrixFold.Cube r)
    (initial final : Bool → MatrixFold.Cube c → Fin k → F)
    (input output : MatrixFold.Cube ((1+r)+c) → Fin k → F)
    (cyclic : ∀ cell row choice,
      input (coordinate cell (AccumulatorShiftQueries.successor row) choice)-output (coordinate cell row choice) =
        impulse start (initial choice cell) row-impulse finish (final choice cell) row) :
    ((shiftWhole coefficient rows half).map (fun branch => branch.fold input)).sum-
      (whole coefficient rows half).fold output =
        correction coefficient half (AccumulatorShiftQueries.weight rows start) initial-
        correction coefficient half (AccumulatorShiftQueries.weight rows finish) final := by
  have block (choice : Bool) :
      rows.fold (fun row => coefficient.fold (fun cell => input (coordinate cell (AccumulatorShiftQueries.successor row) choice)))-
      rows.fold (fun row => coefficient.fold (fun cell => output (coordinate cell row choice))) =
        AccumulatorShiftQueries.weight rows start *ᵥ coefficient.fold (initial choice)-
        AccumulatorShiftQueries.weight rows finish *ᵥ coefficient.fold (final choice) := by
    rw [← fold_sub]
    have combined : (fun row => coefficient.fold (fun cell => input (coordinate cell (AccumulatorShiftQueries.successor row) choice))-
        coefficient.fold (fun cell => output (coordinate cell row choice))) =
        fun row => impulse start (coefficient.fold (initial choice)) row-impulse finish (coefficient.fold (final choice)) row := by
      funext row
      rw [← fold_sub]
      have same : coefficient.fold (fun cell => input (coordinate cell (AccumulatorShiftQueries.successor row) choice)-output (coordinate cell row choice)) =
          coefficient.fold (fun cell => impulse start (initial choice cell) row-impulse finish (final choice cell) row) := by
        apply congrArg coefficient.fold
        funext cell
        exact cyclic cell row choice
      rw [same, fold_sub, coefficient_impulse, coefficient_impulse]
    rw [combined, fold_sub, fold_impulse, fold_impulse]
  rw [shiftWhole_fold, whole_fold]
  calc
    _ = half false *ᵥ
        (rows.fold (fun row => coefficient.fold (fun cell => input (coordinate cell (AccumulatorShiftQueries.successor row) false)))-
          rows.fold (fun row => coefficient.fold (fun cell => output (coordinate cell row false)))) +
        half true *ᵥ
        (rows.fold (fun row => coefficient.fold (fun cell => input (coordinate cell (AccumulatorShiftQueries.successor row) true)))-
          rows.fold (fun row => coefficient.fold (fun cell => output (coordinate cell row true)))) := by
      simp only [Matrix.mulVec_sub]
      abel
    _ = _ := by
      rw [block false, block true]
      simp only [correction, Matrix.mulVec_sub]
      abel

omit [Field F] in
theorem whole_length (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) :
    (whole coefficient rows half).toList.length = c+r+1 := by
  rw [whole_toList]
  simp only [List.length_append, Query.length_toList, List.length_singleton]
  omega

theorem shiftWhole_length (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) :
    (shiftWhole coefficient rows half).length = r+1 := by
  simp only [shiftWhole, List.length_map, AccumulatorShiftQueries.shifted_length]

/-- Original seven source positions: INPUT_ACC, MONOMIAL_PRODUCT,
EXTERNAL_INPUT, OUTPUT_ACC, SUM_PRODUCT, DECOMPOSITION_A, DECOMPOSITION_B.
Each list retains the native per-source opening order and every shift branch. -/
def queries (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (last : MatrixFold.Cube r)
    (role : Fin 7) : List (Query F k ((1+r)+c)) :=
  let base := whole coefficient rows half
  if role.val = 0 then
    base :: whole coefficient (AccumulatorShiftQueries.selected (AccumulatorShiftQueries.zero r)) half ::
      shiftWhole coefficient rows half
  else if role.val = 2 then
    [base,whole coefficient rows (selectHalf half false),whole coefficient rows (selectHalf half true)]
  else if role.val = 3 then
    [base,whole coefficient (AccumulatorShiftQueries.selected last) half]
  else [base]

theorem queries_count (coefficient : Query F k c) (rows : Query F k r)
    (half : MatrixFold.Pair (F := F) (Lane := Fin k)) (last : MatrixFold.Cube r) (role : Fin 7) :
    (queries coefficient rows half last role).length =
      if role.val = 0 then r+3 else if role.val = 2 then 3 else if role.val = 3 then 2 else 1 := by
  unfold queries
  split_ifs <;> simp [shiftWhole_length]

end
end FormalProof4FHE.HasteBoots.AccumulatorPackedQueries
