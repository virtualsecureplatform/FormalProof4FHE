module

public import FormalProof4FHE.HasteBoots.NativeGoldPackedFold

@[expose] public section

/-! Interpretation of packed raw output. The constant shortcut is discharged
using its computed field-equality predicate; no constant-table certificate is
accepted as a protocol input. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning

open NativeFieldRepresentation NativeFields
open NativeGoldPackedFold (Table)
open scoped Matrix

/-- Rectangular list construction has the native contiguous cell addresses. -/
theorem flatten_ofFn {α : Type} (rows width : ℕ) (entry : Fin rows → Fin width → α) :
    (List.ofFn (fun row => List.ofFn (entry row))).flatten =
      List.ofFn (fun address : Fin (rows*width) =>
        let coordinates := finProdFinEquiv.symm address
        entry coordinates.1 coordinates.2) := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext lane
  have address : (⟨row.val*width+lane.val,by
      have := row.isLt; have := lane.isLt; nlinarith⟩ : Fin (rows*width)) = finProdFinEquiv (row,lane) := by
    apply Fin.ext
    change row.val*width+lane.val = lane.val+width*row.val
    ac_rfl
  rw [address,Equiv.symm_apply_apply]

/-- Recover any cell without normalizing its original raw words. -/
theorem flattened_cell (rows width : ℕ) (entry : Fin rows → Fin width → GoldWord) (row : Fin rows) :
    NativeGoldPackedFold.cell ⟨0,width,(List.ofFn (fun row => List.ofFn (entry row))).flatten⟩ row.val =
      List.ofFn (entry row) := by
  rw [NativeGoldPackedFold.cell,flatten_ofFn]
  apply congrArg List.ofFn
  funext lane
  have bound : row.val*width+lane.val < rows*width := by
    have := row.isLt; have := lane.isLt; nlinarith
  have address : (⟨row.val*width+lane.val,bound⟩ : Fin (rows*width)) = finProdFinEquiv (row,lane) := by
    apply Fin.ext
    change row.val*width+lane.val = lane.val+width*row.val
    ac_rfl
  simp only [List.getElem?_ofFn,dite_eq_left bound,address,Equiv.symm_apply_apply,Option.getD_some]

/-- The cell selected by the native branch, retaining its raw representatives. -/
def selected (table : Table) (pair : NativeGoldCoefficientsQuery.Pair) (index : ℕ) : List GoldWord :=
  if NativeGoldPackedFold.constant table then
    NativeGoldPackedFold.combine table.width pair (NativeGoldPackedFold.cell table 0) (NativeGoldPackedFold.cell table 0)
  else NativeGoldPackedFold.combine table.width pair
    (NativeGoldPackedFold.cell table (2*index)) (NativeGoldPackedFold.cell table (2*index+1))

theorem selected_length (table : Table) (pair : NativeGoldCoefficientsQuery.Pair) (index : ℕ) :
    (selected table pair index).length = table.width := by
  simp only [selected,apply_ite List.length,NativeGoldPackedFold.combine_length,ite_self]

/-- A completed fold returns exactly its selected adjacent-cell computation. -/
theorem folded_cell (table : Table) (pair : NativeGoldCoefficientsQuery.Pair)
    (index : Fin (2^(table.numVars-1))) :
    NativeGoldPackedFold.cell ⟨table.numVars-1,table.width,NativeGoldPackedFold.foldedValues table pair⟩ index.val =
      selected table pair index.val := by
  have represented : (List.ofFn (fun index : Fin (2^(table.numVars-1)) => selected table pair index.val)) =
      List.ofFn (fun index : Fin (2^(table.numVars-1)) => List.ofFn (fun lane : Fin table.width =>
        (selected table pair index.val)[lane.val]?.getD 0)) := by
    apply congrArg List.ofFn
    funext index
    exact (NativeGoldPackedFold.ofFn_words _ _ (selected_length _ _ _)).symm
  change NativeGoldPackedFold.cell ⟨table.numVars-1,table.width,
    (List.ofFn (fun index : Fin (2^(table.numVars-1)) => selected table pair index.val)).flatten⟩ index.val = _
  rw [represented]
  change NativeGoldPackedFold.cell ⟨0,table.width,
    (List.ofFn (fun index : Fin (2^(table.numVars-1)) => List.ofFn (fun lane : Fin table.width =>
      (selected table pair index.val)[lane.val]?.getD 0))).flatten⟩ index.val = _
  rw [flattened_cell,NativeGoldPackedFold.ofFn_words _ _ (selected_length _ _ _)]

noncomputable section

/-- Field projection of an original raw cell. Bounds are proved from validation. -/
def value (table : Table) (index : ℕ) : Fin table.width → Goldilocks :=
  fun lane => goldValue (table.values[index*table.width+lane.val]?.getD 0)

theorem cell_value (table : Table) (index : ℕ) :
    (NativeGoldPackedFold.cell table index).map goldValue = List.ofFn (value table index) := by
  rw [NativeGoldPackedFold.cell,List.map_ofFn]
  rfl

theorem constant_value (table : Table) (constantCells : NativeGoldPackedFold.constant table = true)
    (index : Fin (2^table.numVars)) : value table index.val = value table 0 := by
  apply List.ofFn_injective
  rw [← cell_value,← cell_value]
  exact NativeGoldPackedFold.constant_value _ constantCells index

/-- The computed shortcut and the general branch have the same field meaning. -/
theorem selected_value (table : Table) (pair : NativeGoldCoefficientsQuery.Pair)
    (zero : NativeGoldMatrix.validate pair.zero table.width = true)
    (one : NativeGoldMatrix.validate pair.one table.width = true)
    (positive : table.numVars ≠ 0) (index : Fin (2^(table.numVars-1))) :
    (selected table pair index.val).map goldValue = List.ofFn
      (NativeGoldMatrixMeaning.semantic table.width pair.zero zero *ᵥ value table (2*index.val) +
       NativeGoldMatrixMeaning.semantic table.width pair.one one *ᵥ value table (2*index.val+1)) := by
  have size : 2^table.numVars = 2^(table.numVars-1)*2 := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ table.numVars),pow_succ]
  have low : 2*index.val < 2^table.numVars := by rw [size]; have := index.isLt; omega
  have high : 2*index.val+1 < 2^table.numVars := by rw [size]; have := index.isLt; omega
  unfold selected
  split
  · rename_i same
    rw [NativeGoldPackedFold.cell,NativeGoldPackedFold.combine_value _ _ zero one]
    rw [constant_value table same ⟨2*index.val,low⟩,constant_value table same ⟨2*index.val+1,high⟩]
    rfl
  · rw [NativeGoldPackedFold.cell,NativeGoldPackedFold.cell,NativeGoldPackedFold.combine_value _ _ zero one]
    rfl

/-- Native raw folding refines the ordered matrix-vector field operation. -/
theorem folded_cell_value (table : Table) (pair : NativeGoldCoefficientsQuery.Pair)
    (zero : NativeGoldMatrix.validate pair.zero table.width = true)
    (one : NativeGoldMatrix.validate pair.one table.width = true)
    (positive : table.numVars ≠ 0) (index : Fin (2^(table.numVars-1))) :
    (NativeGoldPackedFold.cell ⟨table.numVars-1,table.width,NativeGoldPackedFold.foldedValues table pair⟩ index.val).map goldValue =
      List.ofFn (NativeGoldMatrixMeaning.semantic table.width pair.zero zero *ᵥ value table (2*index.val) +
        NativeGoldMatrixMeaning.semantic table.width pair.one one *ᵥ value table (2*index.val+1)) := by
  rw [folded_cell]
  exact selected_value table pair zero one positive index

/-- Semantic matrices are read from each actual raw query pair. -/
def pairValue (width : ℕ) (pair : NativeGoldCoefficientsQuery.Pair) :
    MatrixFold.Pair (F := Goldilocks) (Lane := Fin width) :=
  fun bit => NativeGoldMatrixWeights.value width (if bit then pair.one else pair.zero)

theorem foldFirst_value (width n : ℕ) (source : List GoldWord) (pair : NativeGoldCoefficientsQuery.Pair)
    (zero : NativeGoldMatrix.validate pair.zero width = true)
    (one : NativeGoldMatrix.validate pair.one width = true) :
    (fun index : Fin (2^n) => value ⟨n,width,NativeGoldPackedFold.foldedValues ⟨n+1,width,source⟩ pair⟩ index.val) =
      FlatMatrixFold.foldFirst (pairValue width pair) (fun index => value ⟨n+1,width,source⟩ index.val) := by
  funext index
  have projected := folded_cell_value ⟨n+1,width,source⟩ pair zero one (Nat.succ_ne_zero n)
    (⟨index.val,by simpa only [Nat.add_sub_cancel_right] using index.isLt⟩ : Fin (2^((n+1)-1)))
  apply List.ofFn_injective
  rw [← cell_value]
  simpa only [Nat.add_sub_cancel_right,FlatMatrixFold.foldFirst,FlatMatrixFold.child,pairValue,
    Bool.false_eq_true,ite_false,ite_true,add_zero,
    NativeGoldMatrixWeights.value_checked width pair.zero zero,
    NativeGoldMatrixWeights.value_checked width pair.one one] using projected

/-- Complete checked raw folding computes the existing ordered flat fold.
The original payload is projected only after its exact bytes have been fixed. -/
theorem loop_value (width : ℕ) (query : List NativeGoldCoefficientsQuery.Pair)
    (source result : List GoldWord)
    (valid : NativeGoldPackedFold.validate ⟨query.length,width,source⟩ = true)
    (queryValid : NativeGoldMatrixWeights.QueryValid width query)
    (success : NativeGoldPackedFold.loop ⟨query.length,width,source⟩ query = some ⟨0,width,result⟩) :
    result.map goldValue = List.ofFn (FlatMatrixFold.foldAll (query.map (pairValue width))
      (fun index => value ⟨query.length,width,source⟩ index.val)) := by
  induction query generalizing source with
  | nil =>
    have same : (⟨0,width,source⟩ : Table) = ⟨0,width,result⟩ := Option.some.inj success
    have wordsSame := congrArg Table.values same
    dsimp only at wordsSame
    subst result
    have size : source.length = width := by
      have size := (NativeGoldPackedFold.validate_iff _).mp valid |>.2.2.2
      simpa only [List.length_nil,pow_zero,one_mul] using size
    rw [List.map_nil,FlatMatrixFold.foldAll]
    rw [← cell_value]
    rw [NativeGoldPackedFold.cell]
    have represented := NativeGoldPackedFold.ofFn_words width source size
    simpa only [Fin.val_zero,zero_mul,zero_add] using congrArg (List.map goldValue) represented.symm
  | cons pair tail ih =>
    obtain ⟨next,advanced,rest⟩ := Option.bind_eq_some_iff.mp success
    have preserved := NativeGoldPackedFold.fold_spec _ next pair advanced
    unfold NativeGoldPackedFold.fold at advanced
    split at advanced
    · rename_i guards
      have same := Option.some.inj advanced
      subst next
      have zero := (queryValid pair List.mem_cons_self).1
      have one := (queryValid pair List.mem_cons_self).2
      have tailValid : NativeGoldMatrixWeights.QueryValid width tail :=
        fun p member => queryValid p (List.mem_cons_of_mem pair member)
      simp only [List.length_cons,Nat.add_sub_cancel_right] at rest preserved
      have previous := ih _ preserved.1 tailValid rest
      rw [previous,List.map_cons,FlatMatrixFold.foldAll]
      congr 1
      congr 1
      funext index
      exact congrFun (foldFirst_value width tail.length source pair zero one)
        ⟨index.val,by simpa only [List.length_map] using index.isLt⟩
    · contradiction

/-- The checked evaluation API inherits the complete ordered-fold semantics. -/
theorem evaluate_value (width : ℕ) (query : List NativeGoldCoefficientsQuery.Pair)
    (source result : List GoldWord) (queryValid : NativeGoldMatrixWeights.QueryValid width query)
    (success : NativeGoldPackedFold.evaluate ⟨query.length,width,source⟩ query = some result) :
    result.map goldValue = List.ofFn (FlatMatrixFold.foldAll (query.map (pairValue width))
      (fun index => value ⟨query.length,width,source⟩ index.val)) := by
  unfold NativeGoldPackedFold.evaluate at success
  split at success
  · rename_i guards
    have valid := (Bool.and_eq_true_iff.mp guards).1
    obtain ⟨next,read,same⟩ := Option.map_eq_some_iff.mp success
    have spec := NativeGoldPackedFold.loop_spec _ next query valid read
    have zero : next.numVars = 0 := by dsimp only at spec; omega
    have widthSame : next.width = width := spec.2.2
    cases next with
    | mk n w values =>
      dsimp only at zero widthSame same
      subst n
      subst w
      subst result
      exact loop_value width query source values valid queryValid read
  · contradiction

end

end FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning
