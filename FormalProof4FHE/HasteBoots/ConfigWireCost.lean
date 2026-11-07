module
public import FormalProof4FHE.HasteBoots.TableWireCost
@[expose] public section

/-! Measured native lookup configuration wire operations. The exact logical
length, nested public table and repetitions are retained; no columns field is
invented. Structural decoding is not a trusted-configuration check. Charges are
abstract byte/list/word operations; physical/native refinement is separate. -/
namespace FormalProof4FHE.HasteBoots.ConfigWireCost
open InputIndexedOracle (Input)
open NativeLookupRequestWire (Config configCodec)
open SolverOperationCost (Run)

def read (input : Input) : Run (Option (Config × Input)) :=
  let logical := IntegerPrefixCost.readUsize input
  match logical.value with
  | none => ⟨none,logical.cost+3⟩
  | some (size,tail) =>
    let table := TableWireCost.read tail
    match table.value with
    | none => ⟨none,logical.cost+table.cost+5⟩
    | some (rows,afterTable) =>
      let repetitions := IntegerPrefixCost.readUsize afterTable
      match repetitions.value with
      | none => ⟨none,logical.cost+table.cost+repetitions.cost+7⟩
      | some (count,rest) => ⟨some (⟨size,rows,count⟩,rest),logical.cost+table.cost+repetitions.cost+8⟩

theorem read_value (input : Input) : (read input).value = configCodec.read input := by
  simp only [configCodec,NativePrefixCodec.transport,NativePrefixCodec.product,NativePrefixCodec.usize,
    ← TableWireCost.read_value]
  cases first : (IntegerPrefixCost.readUsize input).value with
  | none => simp only [read,first,Option.bind_none,Option.map_none]
  | some pair =>
    rcases pair with ⟨size,tail⟩
    simp only [read,first,Option.bind_some]
    cases table : (TableWireCost.read tail).value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨rows,afterTable⟩
      simp only [Option.bind_some]
      cases last : (IntegerPrefixCost.readUsize afterTable).value <;> rfl

theorem read_cost (input : Input) : (read input).cost ≤ 113*(input.length+1)+15 := by
  have logical := IntegerPrefixCost.readUsize_cost input
  simp only [read]
  split
  · dsimp only; omega
  · rename_i size tail first
    have firstSize := IntegerPrefixCost.readUsize_remaining input size tail first
    have table := TableWireCost.read_cost tail
    split
    · dsimp only; omega
    · rename_i rows afterTable decoded
      have success := TableWireCost.read_success_cost tail rows afterTable decoded
      have consumed := TableWireCost.read_remaining tail rows afterTable decoded
      have repetitions := IntegerPrefixCost.readUsize_cost afterTable
      split <;> dsimp only <;> omega

theorem read_remaining (input : Input) (config : Config) (rest : Input)
    (found : (read input).value = some (config,rest)) :
    TableWireCost.cells config.table.val+rest.length+3 ≤ input.length := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i size tail first
    split at found
    · contradiction
    · rename_i rows afterTable decoded
      split at found
      · contradiction
      · rename_i count last parsed
        have left := IntegerPrefixCost.readUsize_remaining input size tail first
        have middle := TableWireCost.read_remaining tail rows afterTable decoded
        have right := IntegerPrefixCost.readUsize_remaining afterTable count last parsed
        have same := Option.some.inj found
        cases same
        dsimp only
        omega

theorem read_success_cost (input : Input) (config : Config) (rest : Input)
    (found : (read input).value = some (config,rest)) :
    (read input).cost ≤ 120*(input.length-rest.length)+1 := by
  have firstCost := IntegerPrefixCost.readUsize_cost input
  simp only [read] at found ⊢
  split at found
  · contradiction
  · rename_i size tail first
    split at found
    · contradiction
    · rename_i rows afterTable decoded
      split at found
      · contradiction
      · rename_i count last parsed
        have tableCost := TableWireCost.read_success_cost tail rows afterTable decoded
        have lastCost := IntegerPrefixCost.readUsize_cost afterTable
        have left := IntegerPrefixCost.readUsize_remaining input size tail first
        have middle := TableWireCost.read_remaining tail rows afterTable decoded
        have right := IntegerPrefixCost.readUsize_remaining afterTable count last parsed
        have same := Option.some.inj found
        cases same
        dsimp only
        omega

def encode (config : Config) : Run Input :=
  let logical := IntegerEncodingCost.encode config.logicalLength
  let table := TableWireCost.encode config.table
  let repetitions := IntegerEncodingCost.encode config.repetitions
  let body := RowEncodingCost.append table.value repetitions.value
  let complete := RowEncodingCost.append logical.value body.value
  ⟨complete.value,logical.cost+table.cost+repetitions.cost+body.cost+complete.cost+5⟩

theorem encode_value (config : Config) : (encode config).value = configCodec.encode config := by
  simp only [encode,RowEncodingCost.append_value,IntegerEncodingCost.encode_value,
    TableWireCost.encode_value,NativeLookupRequestWire.config_encode,List.append_assoc]

theorem encode_cost (config : Config) : (encode config).cost ≤ 156*TableWireCost.cells config.table.val+372 := by
  have logical := IntegerEncodingCost.encode_cost config.logicalLength
  have logicalSize := IntegerEncodingCost.encode_length config.logicalLength
  have table := TableWireCost.encode_cost config.table
  have tableSize := TableWireCost.encode_size config.table
  have repetitions := IntegerEncodingCost.encode_cost config.repetitions
  simp only [encode,RowEncodingCost.append_cost]
  omega

theorem encode_size (config : Config) : (encode config).value.length ≤ 9*TableWireCost.cells config.table.val+27 := by
  have logical := IntegerEncodingCost.encode_length config.logicalLength
  have table := TableWireCost.encode_size config.table
  have repetitions := IntegerEncodingCost.encode_length config.repetitions
  simp only [encode,RowEncodingCost.append_value,List.length_append]
  omega
end FormalProof4FHE.HasteBoots.ConfigWireCost
