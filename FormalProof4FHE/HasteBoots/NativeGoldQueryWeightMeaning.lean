module
public import FormalProof4FHE.HasteBoots.NativeGoldWeightLayout
public import FormalProof4FHE.HasteBoots.NativeGoldQueryGroups
@[expose] public section

/-! Exact ordered prefix grouping preserves semantic left-query matrices,
including aliases whose raw words differ by a field modulus. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldQueryWeightMeaning
open NativeGoldPcsWire (Query Matrix Pair)
open NativeGoldPackedMeaning (pairValue)
open NativeFieldRepresentation (goldValue)
noncomputable section

theorem matrix_value (width : ℕ) (first second : Matrix)
    (equal : NativeGoldQueryGroups.MatrixEqual first second) :
    NativeGoldMatrixWeights.value width first.model = NativeGoldMatrixWeights.value width second.model := by
  funext row column
  have entry :=  congrArg (fun words => (words[row.val*width+column.val]?).getD (goldValue 0)) equal.2
  simpa only [NativeGoldMatrixWeights.value,NativeGoldPcsWire.Matrix.model,List.getElem?_map,Option.getD_map] using entry

theorem pair_value (width : ℕ) (first second : Pair)
    (equal : NativeGoldQueryGroups.PairEqual first second) :
    pairValue width (NativeGoldPcsWire.pairModel first) = pairValue width (NativeGoldPcsWire.pairModel second) := by
  funext bit
  cases bit
  · exact matrix_value width first.1 second.1 equal.1
  · exact matrix_value width first.2 second.2 equal.2

theorem pairs_value (width : ℕ) (first second : List Pair)
    (equal : List.Forall₂ NativeGoldQueryGroups.PairEqual first second) :
    first.map (fun pair => pairValue width (NativeGoldPcsWire.pairModel pair)) =
      second.map (fun pair => pairValue width (NativeGoldPcsWire.pairModel pair)) := by
  induction equal with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons]
    exact congrArg₂ List.cons (pair_value width _ _ head) ih

/-- Group equality retains the original variable order and field projection. -/
theorem prefix_value (width left : ℕ) (first second : Query)
    (equal : NativeGoldQueryGroups.key left first = NativeGoldQueryGroups.key left second) :
    (first.models.take left).map (pairValue width) = (second.models.take left).map (pairValue width) := by
  have paired := (NativeGoldQueryGroups.key_eq_iff left first second).mp equal
  simp only [NativeGoldPcsWire.Query.models,← List.map_take,List.map_map]
  exact pairs_value width _ _ paired

/-- Every original query has the same semantic left prefix as its first
original group owner. Right queries are not part of this equality. -/
theorem representative_prefix (width left : ℕ) (queries : NativePrefixCodec.Vector Query)
    (index : Fin queries.val.length) :
    ((queries.val.get (NativeGoldQueryGroups.representative left queries (NativeGoldQueryGroups.group left queries index))).models.take left).map (pairValue width) =
      ((queries.val.get index).models.take left).map (pairValue width) := by
  apply prefix_value
  rw [NativeGoldQueryGroups.representative_key,NativeGoldQueryGroups.group_key]
end
end FormalProof4FHE.HasteBoots.NativeGoldQueryWeightMeaning
