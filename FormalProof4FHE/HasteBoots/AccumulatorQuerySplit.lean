module
public import FormalProof4FHE.HasteBoots.AccumulatorPackedQueries
@[expose] public section

/-! Query-independent complete source coordinates and exact decomposition of
any complete query into coefficient, row and half blocks. -/
namespace FormalProof4FHE.HasteBoots.AccumulatorQuerySplit
open PackedSumcheckSubclaim (Query)
noncomputable section

def cubeSplit : (front back : ℕ) → MatrixFold.Cube (back+front) ≃ (MatrixFold.Cube front × MatrixFold.Cube back)
  | 0, _ =>
    { toFun := fun cell => ((),cell)
      invFun := fun pair => pair.2
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨emptyCell,cell⟩; cases emptyCell; rfl }
  | front+1, back =>
    (Equiv.prodCongr (Equiv.refl Bool) (cubeSplit front back)).trans (Equiv.prodAssoc _ _ _).symm

theorem cubeSplit_append {front back : ℕ} (first : MatrixFold.Cube front) (last : MatrixFold.Cube back) :
    cubeSplit front back (MonomialBitOrder.append first last) = (first,last) := by
  induction front with
  | zero => cases first; rfl
  | succ front ih =>
    rcases first with ⟨bit,tail⟩
    change ((bit,(cubeSplit front back (MonomialBitOrder.append tail last)).1),
      (cubeSplit front back (MonomialBitOrder.append tail last)).2) = _
    rw [ih]
    rfl

def halfEquiv : MatrixFold.Cube 1 ≃ Bool where
  toFun := Prod.fst
  invFun := fun bit => (bit,())
  left_inv := by rintro ⟨bit,emptyCell⟩; cases emptyCell; rfl
  right_inv := fun _ => rfl

def coordinates (c r : ℕ) : MatrixFold.Cube ((1+r)+c) ≃
    (MatrixFold.Cube c × (MatrixFold.Cube r × Bool)) :=
  (cubeSplit c (1+r)).trans (Equiv.prodCongr (Equiv.refl _) ((cubeSplit r 1).trans
    (Equiv.prodCongr (Equiv.refl _) halfEquiv)))

theorem coordinates_apply {c r : ℕ} (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r) (half : Bool) :
    coordinates c r (AccumulatorPackedQueries.coordinate cell row half) = (cell,(row,half)) := by
  change ((cubeSplit c (1+r) (MonomialBitOrder.append cell (MonomialBitOrder.append row (show MatrixFold.Cube 1 from (half,()))))).1,
    ((cubeSplit r 1 (cubeSplit c (1+r) (MonomialBitOrder.append cell (MonomialBitOrder.append row (show MatrixFold.Cube 1 from (half,()))))).2).1,
    halfEquiv (cubeSplit r 1 (cubeSplit c (1+r) (MonomialBitOrder.append cell (MonomialBitOrder.append row (show MatrixFold.Cube 1 from (half,()))))).2).2)) = _
  rw [cubeSplit_append, cubeSplit_append]
  rfl

theorem coordinates_inverse {c r : ℕ} (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r) (half : Bool) :
    (coordinates c r).symm (cell,(row,half)) = AccumulatorPackedQueries.coordinate cell row half := by
  apply (coordinates c r).injective
  rw [Equiv.apply_symm_apply, coordinates_apply]

variable {F : Type} {k : ℕ}

def querySplit : (front back : ℕ) → Query F k (back+front) → Query F k front × Query F k back
  | 0, _, query => (.nil,query)
  | front+1, back, .cons pair tail =>
    let split := querySplit front back tail
    (.cons pair split.1,split.2)

theorem append_split (front back : ℕ) (query : Query F k (back+front)) :
    AccumulatorPackedQueries.append (querySplit front back query).1 (querySplit front back query).2 = query := by
  induction front with
  | zero => rfl
  | succ front ih =>
    cases query with
    | cons pair tail => exact congrArg (Query.cons pair) (ih tail)

def lastPair : Query F k 1 → MatrixFold.Pair (F := F) (Lane := Fin k)
  | .cons pair .nil => pair

theorem lastPair_rebuild (query : Query F k 1) : Query.cons (lastPair query) .nil = query := by
  cases query with
  | cons pair tail => cases tail; rfl

def parts {c r : ℕ} (query : Query F k ((1+r)+c)) :
    Query F k c × (Query F k r × MatrixFold.Pair (F := F) (Lane := Fin k)) :=
  let first := querySplit c (1+r) query
  let rest := querySplit r 1 first.2
  (first.1,(rest.1,lastPair rest.2))

theorem rebuild {c r : ℕ} (query : Query F k ((1+r)+c)) :
    AccumulatorPackedQueries.whole (parts query).1 (parts query).2.1 (parts query).2.2 = query := by
  simp only [parts, AccumulatorPackedQueries.whole]
  rw [lastPair_rebuild, append_split, append_split]

end
end FormalProof4FHE.HasteBoots.AccumulatorQuerySplit
