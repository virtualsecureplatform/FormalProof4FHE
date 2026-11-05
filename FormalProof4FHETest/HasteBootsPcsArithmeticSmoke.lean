module

import all FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWire

open FormalProof4FHE.HasteBoots

/-! Native arithmetic fixtures at dff353006322693cab3dc6b654f82151f658f294.
Noncommuting two-round queries distinguish product order and block enumeration.
Lazy constant cells distinguish field equality from raw equality. The PCS suffix
uses the response from the honest full-verifier fixture in PcsPreludeSmoke. -/
namespace NativePcsArithmeticSmoke
private noncomputable def word (n : ℕ) : NativeFieldRepresentation.GoldWord := ⟨n % (2^64),Nat.mod_lt _ (by decide)⟩
private noncomputable def words (values : List ℕ) := values.map word
private noncomputable def matrix (values : List ℕ) : NativeGoldMatrix.Matrix := ⟨2,words values⟩
private noncomputable def a : NativeGoldCoefficientsQuery.Pair := ⟨matrix [1,2,3,4],matrix [5,6,7,8]⟩
private noncomputable def b : NativeGoldCoefficientsQuery.Pair := ⟨matrix [2,1,0,3],matrix [4,5,6,7]⟩
private noncomputable def query := [a,b]
private noncomputable def weightWords := (NativeGoldMatrixWeights.weights 2 query).map (fun weights => weights.map (fun matrix => matrix.values.map Fin.val))
example : weightWords = some [[5,8,9,12],[17,20,21,24],[19,28,27,40],[55,64,79,92]] := by decide +kernel
example : (NativeGoldPcsArithmetic.structured 2 2 query).map (List.map Fin.val) =
  some [5,8,17,20,19,28,55,64,9,12,21,24,27,40,79,92] := by decide +kernel
example : (NativeGoldMatrixAccumulate.apply 2 a.zero
    (words [18446744069414584324,18446744069414584325])
    (words [18446744069414584322,18446744069414584323])).map (List.map Fin.val) =
  some [18446744069414584333,18446744069414584348] := by decide +kernel
private noncomputable def general : NativeGoldPackedFold.Table := ⟨2,2,words [0,1,2,3,4,5,6,7]⟩
private noncomputable def lazyConstant : NativeGoldPackedFold.Table :=
  ⟨2,2,words [0,1,18446744069414584321,18446744069414584322,0,18446744069414584322,18446744069414584321,1]⟩
private noncomputable def nearConstant : NativeGoldPackedFold.Table :=
  ⟨2,2,words [0,1,18446744069414584321,18446744069414584322,0,18446744069414584322,18446744069414584321,2]⟩
example : NativeGoldPackedFold.constant general = false := by decide +kernel
example : NativeGoldPackedFold.constant lazyConstant = true := by decide +kernel
example : NativeGoldPackedFold.constant nearConstant = false := by decide +kernel
example : (NativeGoldPackedFold.fold general a).map (fun table => table.values.map Fin.val) = some [30,42,86,130] := by decide +kernel
example : (NativeGoldPackedFold.fold lazyConstant a).map (fun table => table.values.map Fin.val) = some [8,12,8,12] := by decide +kernel
example : (NativeGoldPackedFold.fold nearConstant a).map (fun table => table.values.map Fin.val) =
  some [18446744069414584329,18446744069414584333,18446744069414584335,18446744069414584341] := by decide +kernel
example : (NativeGoldPackedFold.evaluate general query).map (List.map Fin.val) = some [1096,1552] := by decide +kernel
example : (NativeGoldPackedFold.evaluate lazyConstant query).map (List.map Fin.val) = some [120,168] := by decide +kernel
example : (NativeGoldPackedFold.evaluate nearConstant query).map (List.map Fin.val) =
  some [18446744069414584505,18446744069414584581] := by decide +kernel
private noncomputable def point : List NativeFieldWire.GoldExtension := [![word 2,word 3,word 5],![word 7,word 11,word 13]]
private noncomputable def pcsQuery := (NativeGoldCoefficientsQuery.coefficientsQuery 3 point).map NativeGoldCoefficientsQuery.Query.pairs
private noncomputable def response := words [18446744069414584495,18446744069414584501,18446744069414584442,18446744069414584448,18446744069414584353,18446744069414584359]
example : (NativeGoldPcsArithmetic.transpose 3 2 response).map Fin.val =
  [18446744069414584495,18446744069414584442,18446744069414584353,18446744069414584501,18446744069414584448,18446744069414584359] := by decide +kernel
example : (pcsQuery.bind (fun q => NativeGoldPcsArithmetic.finish 2 3 1 q response)).map (List.map Fin.val) =
  some [18446744069414585545,18446744069414585096,18446744069414584539] := by decide +kernel
example : NativeGoldMatrixWeights.start 0 = none := by decide +kernel
example : NativeGoldMatrixWeights.start (2^32) = none := by decide +kernel
example : NativeGoldPcsArithmetic.structured 2 3 query = none := by decide +kernel
example : NativeGoldMatrixAccumulate.apply 2 a.zero (words [1]) (words [1,2]) = none := by decide +kernel
example : NativeGoldPackedFold.validate ⟨64,1,[]⟩ = false := by decide +kernel
example : NativeGoldPackedFold.validate ⟨2,0,[]⟩ = false := by decide +kernel
example : NativeGoldPackedFold.validate ⟨2,2,words [1,2]⟩ = false := by decide +kernel
example : NativeGoldPackedFold.fold ⟨0,2,words [1,2]⟩ a = none := by decide +kernel
example : NativeGoldPackedFold.evaluate general [a] = none := by decide +kernel
example : NativeGoldPackedFold.evaluate ⟨0,2,words [1,2]⟩ [] = some (words [1,2]) := by decide +kernel
example : NativeGoldPcsArithmetic.finish 2 2 3 query (words []) = none := by decide +kernel
example : NativeGoldPcsArithmetic.finish 2 2 1 query (words [1]) = none := by decide +kernel
end NativePcsArithmeticSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.payload_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.payload_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.apply_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.apply_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.payload_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.payload_get

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.zip_ofFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.zip_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.payload_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate.payload_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.identity_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.identity_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.products_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.products_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.products_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.products_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.step_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.step_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.step_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.step_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.loop_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.loop_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.loop_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.weights_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.weights_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.value_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.value_checked

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.result_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.result_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.identity_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.identity_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.products_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.products_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.step_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.loop_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.loop_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.weights_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights.weights_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.validate_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.validate_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.at_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.at_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.address_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.address_bound

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.constant_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.constant_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.combine_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.combine_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.foldedValues_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.foldedValues_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.fold_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.fold_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.fold_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.fold_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.loop_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.evaluate_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.evaluate_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.canonical_map_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.canonical_map_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.ofFn_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.ofFn_words

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.combine_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.combine_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedFold.constant_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedFold.constant_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.flatten_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.flatten_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.flattened_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.flattened_cell

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.selected_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.selected_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.folded_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.folded_cell

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.cell_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.cell_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.constant_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.constant_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.selected_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.selected_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.folded_cell_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.folded_cell_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.foldFirst_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.foldFirst_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.loop_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.loop_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.evaluate_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPackedMeaning.evaluate_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.layout_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.layout_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.structured_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.structured_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.transpose_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.transpose_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.transpose_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.transpose_address

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.finish_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.finish_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.transpose_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.transpose_cell

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.finish_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsArithmetic.finish_value
