module
public import FormalProof4FHE.HasteBoots.NativeGoldOrderedWeights
public import FormalProof4FHE.HasteBoots.RectangularMatrixResponse
@[expose] public section

/-! The actual lane/left-cell/source-lane flat word layout projects to the
rectangular matrix weights. Packing width is independent of code width. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldWeightLayout
open NativeFieldRepresentation (goldValue)
open NativeGoldMatrixWeights (value)
noncomputable section

/-- Addressing a uniform array of blocks preserves their list order. -/
theorem blocks_get {α : Type} {n m : ℕ} (f : Fin n → List α)
    (size : ∀ a, (f a).length = m) (i : Fin n) (j : Fin m) :
    (List.ofFn f).flatten[i.val*m+j.val]? = (f i)[j.val]? := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      rw [List.ofFn_succ,List.flatten_cons,List.getElem?_append_left (by simp [size])]
      simp
    | succ i =>
      rw [List.ofFn_succ,List.flatten_cons,List.getElem?_append_right (by rw [size]; simp only [Fin.val_succ,Nat.add_mul,Nat.one_mul]; omega)]
      have address : i.succ.val*m+j.val-(f 0).length = i.val*m+j.val := by
        simp only [Fin.val_succ,size,Nat.add_mul,Nat.one_mul]
        omega
      rw [address]
      exact ih (fun a => f a.succ) (fun a => size a.succ) i


theorem row_value (width : ℕ) (matrix : NativeGoldMatrix.Matrix) (lane : Fin width)
    (valid : NativeGoldMatrix.validate matrix width = true) :
    (NativeGoldMatrix.row matrix lane.val).map goldValue = List.ofFn (fun channel => value width matrix lane channel) := by
  rw [NativeGoldMatrixMeaning.row_ofFn width matrix lane valid,List.map_ofFn]
  congr 1
  funext channel
  dsimp only [Function.comp_def,value]
  rw [List.getElem?_eq_getElem (by
    rw [(NativeGoldMatrix.validate_iff _ _).mp valid |>.2.2.2]
    exact NativeGoldMatrixMeaning.address_bound width lane channel),Option.getD_some]

theorem layout_value (width : ℕ) (matrices : List NativeGoldMatrix.Matrix)
    (valid : NativeGoldMatrixWeights.Valid width matrices) :
    (NativeGoldPcsArithmetic.layout width matrices).map goldValue =
      (List.ofFn (fun lane : Fin width => (List.ofFn (fun cell : Fin matrices.length =>
        List.ofFn (fun channel : Fin width => value width (matrices.get cell) lane channel))).flatten)).flatten := by
  simp only [NativeGoldPcsArithmetic.layout,List.map_flatten,List.map_ofFn,Function.comp_def,List.map_flatMap]
  congr 1
  apply congrArg List.ofFn
  funext lane
  have rows : matrices.flatMap (fun matrix => (NativeGoldMatrix.row matrix lane.val).map goldValue) =
      matrices.flatMap (fun matrix => List.ofFn (fun channel : Fin width => value width matrix lane channel)) := by
    apply List.flatMap_congr
    intro matrix member
    exact row_value width matrix lane (valid matrix member)
  rw [rows]
  conv_lhs => rw [← List.ofFn_get matrices]
  simp only [List.flatMap,List.map_ofFn,Function.comp_def]

/-- The native checker reads the output lane first, then the Boolean left
cell, then the source lane; this address order is not a matrix transpose. -/
theorem layout_get (width : ℕ) (matrices : List NativeGoldMatrix.Matrix)
    (valid : NativeGoldMatrixWeights.Valid width matrices)
    (lane : Fin width) (cell : Fin matrices.length) (channel : Fin width) :
    goldValue ((NativeGoldPcsArithmetic.layout width matrices)[lane.val*(matrices.length*width)+cell.val*width+channel.val]?.getD 0) =
      value width (matrices.get cell) lane channel := by
  let inner := fun (a : Fin width) =>
    (List.ofFn (fun c : Fin matrices.length => List.ofFn (fun d : Fin width => value width (matrices.get c) a d))).flatten
  have sizes : ∀ a, (inner a).length = matrices.length*width := by
    intro a
    simp [inner,List.length_flatten,List.map_ofFn,List.sum_ofFn]
  let coordinate : Fin (matrices.length*width) := ⟨cell.val*width+channel.val,by
    have := cell.isLt
    have := channel.isLt
    nlinarith⟩
  have read := congrArg (fun words => words[lane.val*(matrices.length*width)+coordinate.val]?) (layout_value width matrices valid)
  change _ = (List.ofFn inner).flatten[lane.val*(matrices.length*width)+coordinate.val]? at read
  rw [blocks_get inner sizes lane coordinate] at read
  change _ = (List.ofFn (fun c : Fin matrices.length => List.ofFn (fun d : Fin width => value width (matrices.get c) lane d))).flatten[cell.val*width+channel.val]? at read
  rw [blocks_get _ (fun _ => List.length_ofFn) cell channel] at read
  simp only [List.getElem?_ofFn,channel.isLt,reduceDIte] at read
  simp only [List.getElem?_map] at read
  rw [Nat.add_assoc]
  change goldValue ((NativeGoldPcsArithmetic.layout width matrices)[lane.val*(matrices.length*width)+coordinate.val]?.getD 0) = _
  cases h : (NativeGoldPcsArithmetic.layout width matrices)[lane.val*(matrices.length*width)+coordinate.val]? with
  | none => simp [h] at read
  | some word => simpa only [h,Option.getD_some] using Option.some.inj (by simpa only [h,Option.map_some] using read)

/-- A computed native weight list, at the exact checker address, is the
rectangular left-weight function. No equality of different query orders is assumed. -/
theorem computed_get (width : ℕ) (query : List NativeGoldCoefficientsQuery.Pair)
    (matrices : List NativeGoldMatrix.Matrix) (positive : width ≠ 0) (fits : width*width < 2^64)
    (valid : NativeGoldMatrixWeights.QueryValid width query)
    (computed : NativeGoldMatrixWeights.weights width query = some matrices)
    (lane : Fin width) (cell : Fin (2^(query.map (NativeGoldPackedMeaning.pairValue width)).length)) (channel : Fin width) :
    goldValue ((NativeGoldPcsArithmetic.layout width matrices)[lane.val*((2^query.length)*width)+cell.val*width+channel.val]?.getD 0) =
      RectangularMatrixResponse.weights (FlatMatrixFold.weights (query.map (NativeGoldPackedMeaning.pairValue width))) lane (cell,channel) := by
  obtain ⟨expected,read,length,checked⟩ := NativeGoldMatrixWeights.weights_complete width query positive fits valid
  have same : expected = matrices := Option.some.inj (read.symm.trans computed)
  subst expected
  let nativeCell : Fin matrices.length := ⟨cell.val,by rw [length]; simpa using cell.isLt⟩
  have semantic := NativeGoldOrderedWeights.weights_value width query matrices positive fits valid computed
  have atCell := congrArg (fun entries => entries[cell.val]?) semantic
  rw [List.getElem?_map,List.getElem?_eq_getElem (show cell.val < matrices.length from nativeCell.isLt),Option.map_some,
    List.getElem?_ofFn,dite_eq_left cell.isLt] at atCell
  have matrixEqual : value width (matrices.get nativeCell) = FlatMatrixFold.weights (query.map (NativeGoldPackedMeaning.pairValue width)) cell :=
    Option.some.inj atCell
  have result := layout_get width matrices checked lane nativeCell channel
  rw [matrixEqual] at result
  simpa only [length,RectangularMatrixResponse.weights,nativeCell] using result

/-- Successful structured-weight computation supplies the rectangular weights
for the original ordered left prefix, using the actual flattened word list. -/
theorem structured_get (width leftVars : ℕ) (query : List NativeGoldCoefficientsQuery.Pair)
    (words : List NativeFieldRepresentation.GoldWord) (positive : width ≠ 0) (fits : width*width < 2^64)
    (valid : NativeGoldMatrixWeights.QueryValid width (query.take leftVars))
    (computed : NativeGoldPcsArithmetic.structured width leftVars query = some words)
    (lane : Fin width) (cell : Fin (2^((query.take leftVars).map (NativeGoldPackedMeaning.pairValue width)).length)) (channel : Fin width) :
    goldValue (words[lane.val*((2^(query.take leftVars).length)*width)+cell.val*width+channel.val]?.getD 0) =
      RectangularMatrixResponse.weights (FlatMatrixFold.weights ((query.take leftVars).map (NativeGoldPackedMeaning.pairValue width))) lane (cell,channel) := by
  unfold NativeGoldPcsArithmetic.structured at computed
  split at computed
  · obtain ⟨matrices,read,same⟩ := Option.map_eq_some_iff.mp computed
    subst words
    exact computed_get width (query.take leftVars) matrices positive fits valid read lane cell channel
  · contradiction

end
end FormalProof4FHE.HasteBoots.NativeGoldWeightLayout
