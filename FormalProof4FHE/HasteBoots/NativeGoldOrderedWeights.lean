module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic

@[expose] public section

/-! Native branch expansion uses low-bit-first addresses and ordered matrix
products. No commutation of query matrices or sorting of query bits is used. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldOrderedWeights
open NativeGoldMatrixWeights (semanticStep semanticLoop)
open NativeGoldPackedMeaning (pairValue)
open NativeGoldCoefficientsQuery (Pair)
open NativeFields (Goldilocks)
noncomputable section

abbrev Mat (width : ℕ) := Matrix (Fin width) (Fin width) Goldilocks

theorem step_length (width : ℕ) (pair : Pair) (source : List (Mat width)) :
    (semanticStep width pair source).length = 2*source.length := by
  simp [semanticStep]; omega

theorem step_get (width : ℕ) (pair : Pair) (source : List (Mat width))
    (bit : Bool) (inner : Fin source.length) :
    (semanticStep width pair source)[source.length*(if bit then 1 else 0)+inner.val]? =
      some (pairValue width pair bit * source.get inner) := by
  cases bit with
  | false =>
    simp only [semanticStep, Bool.false_eq_true, reduceIte, Nat.mul_zero, Nat.zero_add]
    rw [List.getElem?_append_left (by simpa only [List.length_map] using inner.isLt)]
    simp [pairValue, inner.isLt]
  | true =>
    simp only [semanticStep, reduceIte, Nat.mul_one]
    rw [List.getElem?_append_right (by simp)]
    simp [pairValue, inner.isLt]

theorem loop_length (width : ℕ) (query : List Pair) (source : List (Mat width)) :
    (semanticLoop width query source).length = 2^query.length*source.length := by
  induction query generalizing source with
  | nil => simp [semanticLoop]
  | cons pair tail ih =>
    rw [semanticLoop, ih, step_length, List.length_cons, pow_succ]
    ac_rfl

/-- An arbitrary initial list occupies the low address block. Each later
query matrix acts on the left, including for noncommuting matrices. -/
theorem loop_get (width : ℕ) (query : List Pair) (source : List (Mat width))
    (cell : MatrixFold.Cube (query.map (pairValue width)).length) (inner : Fin source.length) :
    (semanticLoop width query source)[source.length*(FlatMatrixFold.index (query.map (pairValue width)).length cell).val+inner.val]? =
      some (MatrixFold.weight (query.map (pairValue width)) cell * source.get inner) := by
  induction query generalizing source with
  | nil =>
    cases cell
    change source[source.length*0+inner.val]? = some (1 * source.get inner)
    simp
  | cons pair tail ih =>
    obtain ⟨bit,suffix⟩ := cell
    let next : Fin (semanticStep width pair source).length :=
      ⟨source.length*(if bit then 1 else 0)+inner.val, by
        rw [step_length]; cases bit <;> simp only [Bool.false_eq_true, reduceIte] <;> omega⟩
    have address : source.length*(FlatMatrixFold.index ((pair :: tail).map (pairValue width)).length (bit,suffix)).val+inner.val =
        (semanticStep width pair source).length*(FlatMatrixFold.index (tail.map (pairValue width)).length suffix).val+next.val := by
      change source.length*(FlatMatrixFold.index ((tail.map (pairValue width)).length+1) (bit,suffix)).val+inner.val = _
      dsimp only [next]
      rw [FlatMatrixFold.index_succ_val,step_length]
      split <;> ring
    rw [semanticLoop,address,ih (semanticStep width pair source) suffix next]
    have read := step_get width pair source bit inner
    have bounded := next.isLt
    rw [List.getElem?_eq_getElem bounded] at read
    have same : (semanticStep width pair source).get next = pairValue width pair bit * source.get inner := Option.some.inj read
    change _ = some ((MatrixFold.weight (tail.map (pairValue width)) suffix * pairValue width pair bit) * source.get inner)
    rw [same,Matrix.mul_assoc]

/-- The native list is indexed by exactly the flat tensor-weight addresses. -/
theorem loop_identity (width : ℕ) (query : List Pair) :
    semanticLoop width query [1] = List.ofFn (FlatMatrixFold.weights (query.map (pairValue width))) := by
  apply List.ext_getElem?
  intro index
  by_cases bound : index < 2^query.length
  · let cell : Fin (2^(query.map (pairValue width)).length) := ⟨index,by simpa using bound⟩
    have read := loop_get width query [1] ((FlatMatrixFold.index (query.map (pairValue width)).length).symm cell) ⟨0,by simp⟩
    simpa [FlatMatrixFold.weights,cell,bound] using read
  · rw [List.getElem?_eq_none (by rw [loop_length]; simpa using Nat.le_of_not_gt bound),
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt bound)]

/-- Actual successful checked native expansion has the ordered flat tensor
semantics, after projecting each raw matrix entry to the field. -/
theorem weights_value (width : ℕ) (query : List Pair) (result : List NativeGoldMatrix.Matrix)
    (positive : width ≠ 0) (fits : width*width < 2^64)
    (valid : NativeGoldMatrixWeights.QueryValid width query)
    (success : NativeGoldMatrixWeights.weights width query = some result) :
    result.map (NativeGoldMatrixWeights.value width) =
      List.ofFn (FlatMatrixFold.weights (query.map (pairValue width))) := by
  rw [NativeGoldMatrixWeights.weights_value width query result positive fits valid success,loop_identity]

end
end FormalProof4FHE.HasteBoots.NativeGoldOrderedWeights
