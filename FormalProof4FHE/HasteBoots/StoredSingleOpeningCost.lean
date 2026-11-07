module
public import FormalProof4FHE.HasteBoots.GoldQueryWireCost
public import FormalProof4FHE.HasteBoots.StoredDigestView
public import FormalProof4FHE.HasteBoots.NativeExactCodec
@[expose] public section

/-! Complete stored single-opening claims with measured query/response reading
and canonicality. The root is not accepted from a prefix while ignoring the
query/values. Raw widths/words and query order are preserved. Structural parsing
is not PCS acceptance or a physical/native refinement theorem. -/
namespace FormalProof4FHE.HasteBoots.StoredSingleOpeningCost
open InputIndexedOracle (Input Byte)
open NativeGoldPcsWire (Query openingCodec)
open NativeLookupRequestWire (Row)
open SolverOperationCost (Run)
structure Stored where
  root : Vector Byte 64
  query : Query
  values : Row

def view (opening : Stored) : NativeRootMessage.Digest × Query × Row :=
  (opening.root.get,opening.query,opening.values)

def read (input : Input) : Run (Option (Stored × Input)) :=
  let root := FixedByteReadCost.read 64 input
  match root.value with
  | none => ⟨none,root.cost+3⟩
  | some (digest,tail) =>
    let query := GoldQueryWireCost.read tail
    match query.value with
    | none => ⟨none,root.cost+query.cost+5⟩
    | some (matrices,afterQuery) =>
      let values := UsizeVectorCost.read afterQuery
      match values.value with
      | none => ⟨none,root.cost+query.cost+values.cost+7⟩
      | some (row,rest) => ⟨some (⟨digest,matrices,row⟩,rest),root.cost+query.cost+values.cost+8⟩

theorem read_value (input : Input) :
    (read input).value.map (fun pair => (view pair.1,pair.2)) = openingCodec.read input := by
  simp only [openingCodec,NativePrefixCodec.product,NativeByteCodec.digest,← FixedByteReadCost.read_value,
    ← GoldQueryWireCost.read_value,NativeLookupRequestWire.rowCodec]
  cases root : (FixedByteReadCost.read 64 input).value with
  | none => simp only [read,root,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨digest,tail⟩
    simp only [read,root,Option.map_some,Option.bind_some]
    cases query : (GoldQueryWireCost.read tail).value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨matrices,afterQuery⟩
      simp only [Option.bind_some]
      cases values : (UsizeVectorCost.read afterQuery).value <;> rfl

theorem read_cost (input : Input) : (read input).cost ≤ 136*(input.length+1)+600 := by
  have root := FixedByteReadCost.read_cost 64 input
  have width := Nat.min_le_left 64 input.length
  simp only [read]
  split
  · dsimp only; omega
  · rename_i digest tail first
    have parts := congrArg List.length (FixedByteReadCost.read_some 64 input digest tail first)
    simp only [List.length_append,Vector.length_toList] at parts
    have query := GoldQueryWireCost.read_cost tail
    split
    · dsimp only; omega
    · rename_i matrices afterQuery parsed
      have success := GoldQueryWireCost.read_success_cost tail matrices afterQuery parsed
      have progress := GoldQueryWireCost.read_size tail matrices afterQuery parsed
      have values := UsizeVectorCost.read_cost afterQuery
      split <;> dsimp only <;> omega

theorem read_remaining (input : Input) (opening : Stored) (rest : Input)
    (found : (read input).value = some (opening,rest)) :
    GoldQueryWireCost.queryWeight opening.query+opening.values.val.length+rest.length+66 ≤ input.length := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i digest tail first
    split at found
    · contradiction
    · rename_i matrices afterQuery parsed
      split at found
      · contradiction
      · rename_i row last decoded
        have root := congrArg List.length (FixedByteReadCost.read_some 64 input digest tail first)
        simp only [List.length_append,Vector.length_toList] at root
        have query := GoldQueryWireCost.read_size tail matrices afterQuery parsed
        have values := UsizeVectorCost.read_remaining afterQuery row last decoded
        have same := Option.some.inj found
        cases same
        dsimp only
        omega

def encode (opening : Stored) : Run Input :=
  let root := StoredDigestView.fromVector opening.root
  let query := GoldQueryWireCost.encode opening.query
  let values := RowEncodingCost.encode opening.values
  let tail := RowEncodingCost.append query.value values.value
  let complete := RowEncodingCost.append root.value.val tail.value
  ⟨complete.value,root.cost+query.cost+values.cost+tail.cost+complete.cost+5⟩

theorem encode_value (opening : Stored) : (encode opening).value = openingCodec.encode (view opening) := by
  simp only [encode,RowEncodingCost.append_value,StoredDigestView.fromVector,GoldQueryWireCost.encode_value,
    RowEncodingCost.encode_value,openingCodec,NativePrefixCodec.product,view,
    NativeByteCodec.digest,NativeByteCodec.fixed,FixedByteReadCost.ofFn_get]

theorem encode_cost (opening : Stored) :
    (encode opening).cost ≤ 277*GoldQueryWireCost.queryWeight opening.query+95*opening.values.val.length+641 := by
  have query := GoldQueryWireCost.encode_cost opening.query
  have querySize := GoldQueryWireCost.encode_size opening.query
  have values := RowEncodingCost.encode_cost opening.values
  simp only [encode,StoredDigestView.fromVector,RowEncodingCost.append_cost,Vector.length_toList]
  omega

def parse (input : Input) : Run (Option Stored) :=
  let result := read input
  match result.value with
  | none => ⟨none,result.cost+2⟩
  | some (opening,rest) => ⟨if rest = [] then some opening else none,result.cost+3⟩

theorem parse_cost (input : Input) : (parse input).cost ≤ 136*(input.length+1)+603 := by
  have cost := read_cost input
  simp only [parse]
  split <;> dsimp only <;> omega

theorem parse_size (input : Input) (opening : Stored) (found : (parse input).value = some opening) :
    GoldQueryWireCost.queryWeight opening.query+opening.values.val.length ≤ input.length := by
  simp only [parse] at found
  split at found
  · contradiction
  · rename_i value rest parsed
    have size := read_remaining input value rest parsed
    split at found
    · have same := Option.some.inj found; subst opening; omega
    · contradiction

def decode (input : Input) : Run (Option Stored) :=
  let parsed := parse input
  match parsed.value with
  | none => ⟨none,parsed.cost+2⟩
  | some opening =>
    let canonical := encode opening
    let compared := BytePrefixMatchCost.equal canonical.value input
    ⟨if compared.value then some opening else none,parsed.cost+canonical.cost+compared.cost+5⟩

theorem decode_value (input : Input) :
    (decode input).value.map view = NativeExactCodec.read openingCodec input := by
  simp only [NativeExactCodec.read,← read_value]
  cases parsed : (read input).value with
  | none => simp only [decode,parse,parsed,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨opening,rest⟩
    by_cases ended : rest = [] <;> by_cases same : openingCodec.encode (view opening) = input <;>
      simp [decode,parse,parsed,ended,same,encode_value,BytePrefixMatchCost.equal_value]

theorem decode_cost (input : Input) : (decode input).cost ≤ 419*input.length+1400 := by
  have parsed := parse_cost input
  simp only [decode]
  split
  · dsimp only; omega
  · rename_i opening found
    have size := parse_size input opening found
    have encoded := encode_cost opening
    have compared := BytePrefixMatchCost.equal_cost (encode opening).value input
    have matched := Nat.min_le_right (encode opening).value.length input.length
    dsimp only
    omega

theorem decode_sound (input : Input) (opening : Stored) (found : (decode input).value = some opening) :
    openingCodec.encode (view opening) = input := by
  have native := decode_value input
  rw [found,Option.map_some] at native
  exact NativeExactCodec.read_sound _ _ _ native.symm

theorem view_injective : Function.Injective view := by
  intro first last same
  have root : first.root = last.root := by
    apply Vector.ext
    intro i hi
    exact congrFun (congrArg Prod.fst same) ⟨i,hi⟩
  have query : first.query = last.query := congrArg (fun value => value.2.1) same
  have values : first.values = last.values := congrArg (fun value => value.2.2) same
  cases first
  cases last
  cases root
  cases query
  cases values
  rfl

theorem decode_encode (opening : Stored) : (decode (encode opening).value).value = some opening := by
  have accepted : NativeExactCodec.read openingCodec (encode opening).value = some (view opening) := by
    rw [encode_value]
    exact NativeExactCodec.read_encode _ _
  have native := (decode_value (encode opening).value).trans accepted
  cases parsed : (decode (encode opening).value).value with
  | none => rw [parsed,Option.map_none] at native; cases native
  | some values => rw [parsed,Option.map_some] at native; exact congrArg some (view_injective (Option.some.inj native))
end FormalProof4FHE.HasteBoots.StoredSingleOpeningCost
