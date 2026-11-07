module
public import FormalProof4FHE.HasteBoots.BytePrefixMatchCost
public import FormalProof4FHE.HasteBoots.RowEncodingCost
public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
@[expose] public section

/-! Strict native leaf-role decoding with measured parsing, canonical
serialization and exact byte matching. Costs use the abstract byte/access/word
arithmetic/control model; compiler and physical/backend refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.CostedMerkleLeaf
open InputIndexedOracle (Input)
open NativeLookupRequestWire (Row rowCodec)
open NativeGoldColumnAuthentication (leafInput)
open NativeFieldWire (columnDomain)
open SolverOperationCost (Run)

def encode (row : Row) : Run Input :=
  let body := RowEncodingCost.encode row
  let joined := RowEncodingCost.append columnDomain body.value
  ⟨joined.value,body.cost+joined.cost+2⟩

theorem encode_value (row : Row) : (encode row).value = leafInput row := by
  simp only [encode,RowEncodingCost.append_value,RowEncodingCost.encode_value,leafInput]

theorem encode_cost (row : Row) :
    (encode row).cost ≤ 95*row.val.length+3*columnDomain.length+96 := by
  have body := RowEncodingCost.encode_cost row
  simp only [encode,RowEncodingCost.append_cost]
  omega

def parse (input : Input) : Run (Option Row) :=
  let domain := BytePrefixMatchCost.matchPrefix columnDomain input
  match domain.value with
  | none => ⟨none,domain.cost+3⟩
  | some tail =>
    let decoded := UsizeVectorCost.read tail
    match decoded.value with
    | none => ⟨none,domain.cost+decoded.cost+5⟩
    | some (row,rest) =>
      ⟨if rest = [] then some row else none,domain.cost+decoded.cost+7⟩

theorem parse_value (input : Input) :
    (parse input).value =
      if input.take columnDomain.length = columnDomain then
        (rowCodec.read (input.drop columnDomain.length)).bind (fun parsed =>
          if parsed.2 = [] then some parsed.1 else none)
      else none := by
  by_cases prefixOK : input.take columnDomain.length = columnDomain
  · simp only [parse,BytePrefixMatchCost.matchPrefix_value,prefixOK,ite_true,rowCodec]
    cases (UsizeVectorCost.read (input.drop columnDomain.length)).value with
    | none => rfl
    | some pair => rcases pair with ⟨row,rest⟩; rfl
  · simp only [parse,BytePrefixMatchCost.matchPrefix_value,prefixOK,ite_false]

theorem parse_cost (input : Input) :
    (parse input).cost ≤ 107*(input.length+1)+6*columnDomain.length+16 := by
  have domain := BytePrefixMatchCost.matchPrefix_cost columnDomain input
  simp only [parse]
  split
  · dsimp only; omega
  · rename_i tail found
    have splitInput := (BytePrefixMatchCost.matchPrefix_some columnDomain input tail).mp found
    have size : tail.length ≤ input.length := by rw [splitInput,List.length_append]; omega
    have decoded := UsizeVectorCost.read_cost tail
    split <;> dsimp only <;> omega

theorem parse_size (input : Input) (row : Row) (found : (parse input).value = some row) :
    row.val.length ≤ input.length := by
  simp only [parse] at found
  split at found
  · contradiction
  · rename_i tail domain
    have splitInput := (BytePrefixMatchCost.matchPrefix_some columnDomain input tail).mp domain
    split at found
    · contradiction
    · rename_i values rest decoded
      have size := UsizeVectorCost.read_remaining tail values rest decoded
      split at found
      · have same := Option.some.inj found
        subst row
        rw [splitInput,List.length_append]
        omega
      · contradiction

def decode (input : Input) : Run (Option Row) :=
  let parsed := parse input
  match parsed.value with
  | none => ⟨none,parsed.cost+2⟩
  | some row =>
    let canonical := encode row
    let comparedBytes := BytePrefixMatchCost.equal canonical.value input
    ⟨if comparedBytes.value then some row else none,parsed.cost+canonical.cost+comparedBytes.cost+5⟩

theorem decode_value (input : Input) :
    (decode input).value =
      ((if input.take columnDomain.length = columnDomain then
        (rowCodec.read (input.drop columnDomain.length)).bind (fun parsed =>
          if parsed.2 = [] then some parsed.1 else none)
      else none) : Option Row).bind (fun row => if leafInput row = input then some row else none) := by
  rw [← parse_value]
  simp only [decode]
  cases parsed : (parse input).value with
  | none => rfl
  | some row =>
    simp only [Option.bind_some,encode_value,BytePrefixMatchCost.equal_value]
    by_cases same : leafInput row = input <;> simp [same]

theorem decode_cost (input : Input) :
    (decode input).cost ≤ 208*(input.length+1)+9*columnDomain.length+25 := by
  have parsedCost := parse_cost input
  simp only [decode]
  split
  · dsimp only; omega
  · rename_i row found
    have size := parse_size input row found
    have encoded := encode_cost row
    have matched := BytePrefixMatchCost.equal_cost (encode row).value input
    dsimp only
    omega
end FormalProof4FHE.HasteBoots.CostedMerkleLeaf
