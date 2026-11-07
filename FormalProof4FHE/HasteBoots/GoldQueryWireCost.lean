module
public import FormalProof4FHE.HasteBoots.VectorWireEncodeCost
public import FormalProof4FHE.HasteBoots.NativeGoldPcsWire
public import FormalProof4FHE.HasteBoots.UsizeVectorSuccessCost
@[expose] public section

/-! Closed measured native matrix-pair query wire operations. Widths and every
raw u64 value retain their original spelling and order. Local extension post-maps
are not serialized. Structural recognition is not matrix/parameter validation;
physical/native refinement remains separate. -/
namespace FormalProof4FHE.HasteBoots.GoldQueryWireCost
open InputIndexedOracle (Input)
open NativeGoldPcsWire (Matrix Pair Query matrixCodec pairCodec queryCodec)
open SolverOperationCost (Run)

def matrixWeight (matrix : Matrix) := matrix.values.val.length+1

def readMatrix (input : Input) : Run (Option (Matrix × Input)) :=
  let width := IntegerPrefixCost.readUsize input
  match width.value with
  | none => ⟨none,width.cost+3⟩
  | some (size,tail) =>
    let values := UsizeVectorCost.read tail
    match values.value with
    | none => ⟨none,width.cost+values.cost+5⟩
    | some (row,rest) => ⟨some (⟨size,row⟩,rest),width.cost+values.cost+6⟩

theorem readMatrix_value (input : Input) : (readMatrix input).value = matrixCodec.read input := by
  simp only [matrixCodec,NativePrefixCodec.transport,NativePrefixCodec.product,NativePrefixCodec.usize,
    NativeLookupRequestWire.rowCodec]
  cases first : (IntegerPrefixCost.readUsize input).value with
  | none => simp only [readMatrix,first,Option.bind_none,Option.map_none]
  | some pair =>
    rcases pair with ⟨size,tail⟩
    simp only [readMatrix,first,Option.bind_some]
    cases last : (UsizeVectorCost.read tail).value <;> rfl

theorem readMatrix_size (input : Input) (matrix : Matrix) (rest : Input)
    (found : (readMatrix input).value = some (matrix,rest)) : matrixWeight matrix+rest.length+1 ≤ input.length := by
  simp only [readMatrix] at found
  split at found
  · contradiction
  · rename_i width tail first
    split at found
    · contradiction
    · rename_i values last parsed
      have left := IntegerPrefixCost.readUsize_remaining input width tail first
      have right := UsizeVectorCost.read_remaining tail values last parsed
      have same := Option.some.inj found
      cases same
      dsimp only [matrixWeight]
      omega

theorem readMatrix_progress (input : Input) (matrix : Matrix) (rest : Input)
    (found : (readMatrix input).value = some (matrix,rest)) : rest.length < input.length := by
  have size := readMatrix_size input matrix rest found
  omega

theorem readMatrix_cost (input : Input) : (readMatrix input).cost ≤ 120*(input.length+1) := by
  have width := IntegerPrefixCost.readUsize_cost input
  simp only [readMatrix]
  split
  · dsimp only; omega
  · rename_i size tail parsed
    have progress := IntegerPrefixCost.readUsize_remaining input size tail parsed
    have values := UsizeVectorCost.read_cost tail
    split <;> dsimp only <;> omega

theorem readMatrix_success_cost (input : Input) (matrix : Matrix) (rest : Input)
    (found : (readMatrix input).value = some (matrix,rest)) :
    (readMatrix input).cost ≤ 120*(input.length-rest.length)+1 := by
  have width := IntegerPrefixCost.readUsize_cost input
  simp only [readMatrix] at found ⊢
  split at found
  · contradiction
  · rename_i size tail first
    split at found
    · contradiction
    · rename_i values last parsed
      have left := IntegerPrefixCost.readUsize_remaining input size tail first
      have right := UsizeVectorCost.read_remaining tail values last parsed
      have body := UsizeVectorSuccessCost.read_cost tail values last parsed
      have same := Option.some.inj found
      cases same
      dsimp only
      omega

def pairWeight (pair : Pair) := matrixWeight pair.1+matrixWeight pair.2+1

def readPair (input : Input) : Run (Option (Pair × Input)) :=
  let first := readMatrix input
  match first.value with
  | none => ⟨none,first.cost+3⟩
  | some (zero,tail) =>
    let second := readMatrix tail
    match second.value with
    | none => ⟨none,first.cost+second.cost+5⟩
    | some (one,rest) => ⟨some ((zero,one),rest),first.cost+second.cost+6⟩

theorem readPair_value (input : Input) : (readPair input).value = pairCodec.read input := by
  simp only [pairCodec,NativePrefixCodec.product,← readMatrix_value]
  cases first : (readMatrix input).value with
  | none => simp only [readPair,first,Option.bind_none]
  | some pair =>
    rcases pair with ⟨zero,tail⟩
    simp only [readPair,first,Option.bind_some]
    cases last : (readMatrix tail).value <;> rfl

theorem readPair_size (input : Input) (pair : Pair) (rest : Input)
    (found : (readPair input).value = some (pair,rest)) : pairWeight pair+rest.length+1 ≤ input.length := by
  simp only [readPair] at found
  split at found
  · contradiction
  · rename_i zero tail first
    split at found
    · contradiction
    · rename_i one last parsed
      have left := readMatrix_size input zero tail first
      have right := readMatrix_size tail one last parsed
      have same := Option.some.inj found
      cases same
      dsimp only [pairWeight]
      omega

theorem readPair_progress (input : Input) (pair : Pair) (rest : Input)
    (found : (readPair input).value = some (pair,rest)) : rest.length < input.length := by
  have size := readPair_size input pair rest found
  omega

theorem readPair_cost (input : Input) : (readPair input).cost ≤ 130*(input.length+1) := by
  have first := readMatrix_cost input
  simp only [readPair]
  split
  · dsimp only; omega
  · rename_i zero tail parsed
    have success := readMatrix_success_cost input zero tail parsed
    have progress := readMatrix_progress input zero tail parsed
    have second := readMatrix_cost tail
    split <;> dsimp only <;> omega

theorem readPair_success_cost (input : Input) (pair : Pair) (rest : Input)
    (found : (readPair input).value = some (pair,rest)) :
    (readPair input).cost ≤ 130*(input.length-rest.length)+1 := by
  simp only [readPair] at found ⊢
  split at found
  · contradiction
  · rename_i zero tail first
    split at found
    · contradiction
    · rename_i one last parsed
      have left := readMatrix_success_cost input zero tail first
      have right := readMatrix_success_cost tail one last parsed
      have firstSize := readMatrix_size input zero tail first
      have secondSize := readMatrix_size tail one last parsed
      have same := Option.some.inj found
      cases same
      dsimp only
      omega

def queryWeight (query : Query) := VectorWireReadCost.weight pairWeight query.val

def read (input : Input) : Run (Option (Query × Input)) := VectorWireReadCost.read readPair input

theorem read_value (input : Input) : (read input).value = queryCodec.read input :=
  VectorWireReadCost.read_value readPair pairCodec readPair_value input

theorem read_size (input : Input) (query : Query) (rest : Input)
    (found : (read input).value = some (query,rest)) : queryWeight query+rest.length+1 ≤ input.length :=
  VectorWireReadCost.read_size readPair pairWeight readPair_size input query rest found

theorem read_cost (input : Input) : (read input).cost ≤ 136*(input.length+1)+3 :=
  VectorWireReadCost.read_cost readPair 130 (by decide) readPair_cost readPair_success_cost readPair_progress input

theorem read_success_cost (input : Input) (query : Query) (rest : Input)
    (found : (read input).value = some (query,rest)) : (read input).cost ≤ 136*(input.length-rest.length)+1 :=
  VectorWireReadCost.read_success_cost readPair 130 (by decide) readPair_success_cost readPair_progress input query rest found

def encodeMatrix (matrix : Matrix) : Run Input :=
  let width := IntegerEncodingCost.encode matrix.width
  let values := RowEncodingCost.encode matrix.values
  let joined := RowEncodingCost.append width.value values.value
  ⟨joined.value,width.cost+values.cost+joined.cost+3⟩

theorem encodeMatrix_value (matrix : Matrix) : (encodeMatrix matrix).value = matrixCodec.encode matrix := by
  simp only [encodeMatrix,RowEncodingCost.append_value,IntegerEncodingCost.encode_value,
    RowEncodingCost.encode_value,NativeGoldPcsWire.matrix_encode]

theorem encodeMatrix_cost (matrix : Matrix) : (encodeMatrix matrix).cost ≤ 183*(matrixWeight matrix+1) := by
  have width := IntegerEncodingCost.encode_cost matrix.width
  have size := IntegerEncodingCost.encode_length matrix.width
  have values := RowEncodingCost.encode_cost matrix.values
  simp only [encodeMatrix,RowEncodingCost.append_cost,matrixWeight]
  omega

theorem encodeMatrix_size (matrix : Matrix) : (encodeMatrix matrix).value.length ≤ 9*(matrixWeight matrix+1) := by
  have width := IntegerEncodingCost.encode_length matrix.width
  have values := RowEncodingCost.encode_length matrix.values
  simp only [encodeMatrix,RowEncodingCost.append_value,List.length_append,matrixWeight]
  omega

def encodePair (pair : Pair) : Run Input :=
  let zero := encodeMatrix pair.1
  let one := encodeMatrix pair.2
  let joined := RowEncodingCost.append zero.value one.value
  ⟨joined.value,zero.cost+one.cost+joined.cost+3⟩

theorem encodePair_value (pair : Pair) : (encodePair pair).value = pairCodec.encode pair := by
  simp only [encodePair,RowEncodingCost.append_value,encodeMatrix_value,NativeGoldPcsWire.pair_encode]

theorem encodePair_cost (pair : Pair) : (encodePair pair).cost ≤ 214*(pairWeight pair+1) := by
  have zero := encodeMatrix_cost pair.1
  have one := encodeMatrix_cost pair.2
  have size := encodeMatrix_size pair.1
  simp only [encodePair,RowEncodingCost.append_cost,pairWeight]
  omega

theorem encodePair_size (pair : Pair) : (encodePair pair).value.length ≤ 9*(pairWeight pair+1) := by
  have zero := encodeMatrix_size pair.1
  have one := encodeMatrix_size pair.2
  simp only [encodePair,RowEncodingCost.append_value,List.length_append,pairWeight]
  omega

def encode (query : Query) : Run Input := VectorWireEncodeCost.encode encodePair query

theorem encode_value (query : Query) : (encode query).value = queryCodec.encode query :=
  VectorWireEncodeCost.encode_value encodePair pairCodec encodePair_value query

theorem encode_cost (query : Query) : (encode query).cost ≤ 250*queryWeight query+93 :=
  VectorWireEncodeCost.encode_cost encodePair pairWeight 214 encodePair_cost encodePair_size query

theorem encode_size (query : Query) : (encode query).value.length ≤ 9*(queryWeight query+1) :=
  VectorWireEncodeCost.encode_size encodePair pairWeight encodePair_size query
end FormalProof4FHE.HasteBoots.GoldQueryWireCost
