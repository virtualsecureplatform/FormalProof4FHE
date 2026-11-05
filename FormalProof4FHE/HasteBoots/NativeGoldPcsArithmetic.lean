module

public import FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning

@[expose] public section

/-! Raw structured weights and response transposition for single-opening PCS.
The checked wrappers make native slice/allocation preconditions explicit.
Neither computes a row-code encoding nor asserts PCS acceptance. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic

open NativeFieldRepresentation
open NativeGoldCoefficientsQuery (Pair)

/-- Lane-major order: lane, left Boolean cell, source lane. -/
def layout (width : ℕ) (weights : List NativeGoldMatrix.Matrix) : List GoldWord :=
  (List.ofFn (fun lane : Fin width => weights.flatMap
    (fun matrix => NativeGoldMatrix.row matrix lane.val))).flatten

def structured (width leftVars : ℕ) (query : List Pair) : Option (List GoldWord) :=
  if leftVars ≤ query.length then
    (NativeGoldMatrixWeights.weights width (query.take leftVars)).map (layout width)
  else none

/-- Copy the lane-major response into Boolean-cell-major order. -/
def transpose (width columns : ℕ) (response : List GoldWord) : List GoldWord :=
  (List.ofFn (fun cell : Fin columns => List.ofFn (fun lane : Fin width =>
    response[lane.val*columns+cell.val]?.getD 0))).flatten

/-- Checked wrapper for the constructor-validated native private finish routine. -/
def finish (numVars width leftVars : ℕ) (query : List Pair) (response : List GoldWord) : Option (List GoldWord) :=
  if numVars < 64 ∧ leftVars ≤ numVars ∧ query.length = numVars then
    let remaining := numVars-leftVars
    if response.length = width*2^remaining then
      NativeGoldPackedFold.evaluate ⟨remaining,width,transpose width (2^remaining) response⟩ (query.drop leftVars)
    else none
  else none

theorem layout_length (width : ℕ) (weights : List NativeGoldMatrix.Matrix)
    (valid : NativeGoldMatrixWeights.Valid width weights) :
    (layout width weights).length = width*(weights.length*width) := by
  have rows (lane : Fin width) : (weights.flatMap (fun matrix => NativeGoldMatrix.row matrix lane.val)).length = weights.length*width := by
    induction weights with
    | nil => simp
    | cons matrix tail ih =>
      have good := valid matrix List.mem_cons_self
      rw [List.flatMap_cons,List.length_append,NativeGoldMatrixMeaning.row_length width matrix lane good,
        ih (fun m member => valid m (List.mem_cons_of_mem matrix member)),List.length_cons]
      simp only [Nat.add_mul,Nat.one_mul]
      omega
  simp only [layout,List.length_flatten,List.map_ofFn,Function.comp_def,rows,List.sum_ofFn,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- Valid checked queries always construct exactly the native structured matrix size. -/
theorem structured_complete (width leftVars : ℕ) (query : List Pair) (positive : width ≠ 0)
    (fits : width*width < 2^64) (prefixBound : leftVars ≤ query.length)
    (valid : NativeGoldMatrixWeights.QueryValid width query) :
    ∃ result, structured width leftVars query = some result ∧ result.length = width*(2^leftVars*width) := by
  have prefixValid : NativeGoldMatrixWeights.QueryValid width (query.take leftVars) := by
    intro pair member
    exact valid pair (List.mem_of_mem_take member)
  obtain ⟨weights,read,size,weightsValid⟩ := NativeGoldMatrixWeights.weights_complete width
    (query.take leftVars) positive fits prefixValid
  refine ⟨layout width weights,?_,?_⟩
  · simp only [structured,ite_eq_left prefixBound,read,Option.map_some]
  · rw [layout_length width weights weightsValid,size,List.length_take,Nat.min_eq_left prefixBound]

theorem transpose_length (width columns : ℕ) (response : List GoldWord) :
    (transpose width columns response).length = columns*width := by
  simp [transpose,List.length_flatten,List.map_ofFn,Function.comp_def]

theorem transpose_address (width columns : ℕ) (response : List GoldWord)
    (size : response.length = width*columns) (cell : Fin columns) (lane : Fin width) :
    lane.val*columns+cell.val < response.length := by
  rw [size]
  have := lane.isLt
  have := cell.isLt
  nlinarith

/-- Successful suffix evaluation returns exactly the original packing width. -/
theorem finish_length (numVars width leftVars : ℕ) (query : List Pair) (response result : List GoldWord)
    (success : finish numVars width leftVars query response = some result) : result.length = width := by
  unfold finish at success
  split at success
  · dsimp only at success
    split at success
    · exact NativeGoldPackedFold.evaluate_length _ _ _ success
    · contradiction
  · contradiction

noncomputable section

/-- Transposition preserves each raw response entry at its native address. -/
theorem transpose_cell (width columns : ℕ) (response : List GoldWord) (index : Fin columns) :
    NativeGoldPackedFold.cell ⟨0,width,transpose width columns response⟩ index.val =
      List.ofFn (fun lane : Fin width => response[lane.val*columns+index.val]?.getD 0) :=
  NativeGoldPackedMeaning.flattened_cell columns width _ index

/-- The actual suffix program computes the existing flat MW-MLE fold of the
original lane-major response. Constant shortcuts require no extra premise. -/
theorem finish_value (numVars width leftVars : ℕ) (query : List Pair) (response result : List GoldWord)
    (queryValid : NativeGoldMatrixWeights.QueryValid width query)
    (success : finish numVars width leftVars query response = some result) :
    result.map goldValue = List.ofFn (FlatMatrixFold.foldAll
      ((query.drop leftVars).map (NativeGoldPackedMeaning.pairValue width))
      (fun index lane => goldValue (response[lane.val*2^(numVars-leftVars)+index.val]?.getD 0))) := by
  unfold finish at success
  split at success
  · rename_i guards
    dsimp only at success
    split at success
    · have length : (query.drop leftVars).length = numVars-leftVars := by
        rw [List.length_drop,guards.2.2]
      have suffixValid : NativeGoldMatrixWeights.QueryValid width (query.drop leftVars) :=
        fun pair member => queryValid pair (List.mem_of_mem_drop member)
      rw [← length] at success
      have previous := NativeGoldPackedMeaning.evaluate_value width (query.drop leftVars) _ result suffixValid success
      rw [previous]
      congr 1
      congr 1
      funext index
      apply List.ofFn_injective
      rw [← NativeGoldPackedMeaning.cell_value]
      change (NativeGoldPackedFold.cell ⟨0,width,transpose width (2^(query.drop leftVars).length) response⟩ index.val).map goldValue = _
      rw [transpose_cell width _ response ⟨index.val,by simpa only [List.length_map] using index.isLt⟩]
      simp only [List.map_ofFn,Function.comp_def]
      rw [length]
    · contradiction
  · contradiction

end

end FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic
