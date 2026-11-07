module
public import FormalProof4FHE.HasteBoots.GoldBatchQueriesCost
public import FormalProof4FHE.HasteBoots.StoredSourceVectorCost
public import FormalProof4FHE.HasteBoots.TableWireCost
public import FormalProof4FHE.HasteBoots.NativeGoldBatchMessage
public import FormalProof4FHE.HasteBoots.StoredDigestView
public import FormalProof4FHE.HasteBoots.NativeExactCodec
@[expose] public section

/-! Complete original batch-message decoding with all nested queries and values
retained. EOF and canonical serialization are checked with measured operations.
Structural decoding does not establish verify_many acceptance or physical cost. -/
namespace FormalProof4FHE.HasteBoots.StoredBatchMessageCost
open InputIndexedOracle (Input Byte)
open NativeGoldBatchMessage (codec)
open StoredSourceVectorReadCost (Source)
open NativeLookupRequestWire (Table)
open SolverOperationCost (Run)
structure Stored where
  source : Source
  queries : GoldBatchQueriesCost.Queries
  values : Table

def view (batch : Stored) : NativeGoldBatchMessage.Data :=
  ⟨batch.source.1.get,batch.source.2.get,batch.queries,batch.values⟩

def read (input : Input) : Run (Option (Stored × Input)) :=
  let root := StoredSourceVectorReadCost.readSource input
  match root.value with
  | none => ⟨none,root.cost+3⟩
  | some (digest,tail) =>
    let query := GoldBatchQueriesCost.read tail
    match query.value with
    | none => ⟨none,root.cost+query.cost+5⟩
    | some (matrices,afterQuery) =>
      let values := TableWireCost.read afterQuery
      match values.value with
      | none => ⟨none,root.cost+query.cost+values.cost+7⟩
      | some (row,rest) => ⟨some (⟨digest,matrices,row⟩,rest),root.cost+query.cost+values.cost+8⟩

theorem read_value (input : Input) :
    (read input).value.map (fun pair => (view pair.1,pair.2)) = codec.read input := by
  have tableRead (bytes : Input) : (TableWireCost.read bytes).value =
      (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec).read bytes := TableWireCost.read_value bytes
  simp only [read,StoredSourceVectorReadCost.readSource,codec,NativePrefixCodec.transport,
    NativePrefixCodec.product,NativeByteCodec.digest,← FixedByteReadCost.read_value,
    ← GoldBatchQueriesCost.read_value,← tableRead]
  cases first : (FixedByteReadCost.read 64 input).value with
  | none => simp only [Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨context,tail⟩
    simp only [Option.map_some,Option.bind_some]
    cases second : (FixedByteReadCost.read 64 tail).value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨root,afterRoot⟩
      simp only [Option.map_some,Option.bind_some]
      cases queries : (GoldBatchQueriesCost.read afterRoot).value with
      | none => rfl
      | some pair =>
        rcases pair with ⟨queries,afterQueries⟩
        simp only [Option.bind_some]
        cases values : (TableWireCost.read afterQueries).value <;> rfl

theorem read_cost (input : Input) : (read input).cost ≤ 145*(input.length+1)+1100 := by
  have root := StoredSourceVectorReadCost.readSource_cost input
  simp only [read]
  split
  · dsimp only; omega
  · rename_i digest tail first
    have parts := StoredSourceVectorReadCost.readSource_remaining input digest tail first
    have query := GoldBatchQueriesCost.read_cost tail
    split
    · dsimp only; omega
    · rename_i matrices afterQuery parsed
      have success := GoldBatchQueriesCost.read_success_cost tail matrices afterQuery parsed
      have progress := GoldBatchQueriesCost.read_size tail matrices afterQuery parsed
      have values := TableWireCost.read_cost afterQuery
      split <;> dsimp only <;> omega

theorem read_remaining (input : Input) (opening : Stored) (rest : Input)
    (found : (read input).value = some (opening,rest)) :
    GoldBatchQueriesCost.weight opening.queries+TableWireCost.cells opening.values.val+rest.length+130 ≤ input.length := by
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
        have root := StoredSourceVectorReadCost.readSource_remaining input digest tail first
        have query := GoldBatchQueriesCost.read_size tail matrices afterQuery parsed
        have values := TableWireCost.read_remaining afterQuery row last decoded
        have same := Option.some.inj found
        cases same
        dsimp only
        omega

def encode (opening : Stored) : Run Input :=
  let root := StoredSourceVectorCost.sourceBytes opening.source
  let query := GoldBatchQueriesCost.encode opening.queries
  let values := TableWireCost.encode opening.values
  let tail := RowEncodingCost.append query.value values.value
  let complete := RowEncodingCost.append root.value tail.value
  ⟨complete.value,root.cost+query.cost+values.cost+tail.cost+complete.cost+5⟩

theorem encode_value (opening : Stored) : (encode opening).value = codec.encode (view opening) := by
  simp only [encode,RowEncodingCost.append_value,StoredSourceVectorCost.sourceBytes_value,
    GoldBatchQueriesCost.encode_value,TableWireCost.encode_value,NativeGoldBatchMessage.encode,
    view,NativeLookupRequestWire.tableCodec,FixedByteReadCost.ofFn_get,List.append_assoc]

theorem encode_cost (opening : Stored) :
    (encode opening).cost ≤ 406*GoldBatchQueriesCost.weight opening.queries+129*TableWireCost.cells opening.values.val+1059 := by
  have query := GoldBatchQueriesCost.encode_cost opening.queries
  have querySize := GoldBatchQueriesCost.encode_size opening.queries
  have values := TableWireCost.encode_cost opening.values
  have root := StoredSourceVectorCost.sourceBytes_cost opening.source
  have rootSize := StoredSourceVectorCost.sourceBytes_size opening.source
  simp only [encode,RowEncodingCost.append_cost]
  omega

def parse (input : Input) : Run (Option Stored) :=
  let result := read input
  match result.value with
  | none => ⟨none,result.cost+2⟩
  | some (opening,rest) => ⟨if rest = [] then some opening else none,result.cost+3⟩

theorem parse_cost (input : Input) : (parse input).cost ≤ 145*(input.length+1)+1103 := by
  have cost := read_cost input
  simp only [parse]
  split <;> dsimp only <;> omega

theorem parse_size (input : Input) (opening : Stored) (found : (parse input).value = some opening) :
    GoldBatchQueriesCost.weight opening.queries+TableWireCost.cells opening.values.val ≤ input.length := by
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
    (decode input).value.map view = NativeExactCodec.read codec input := by
  simp only [NativeExactCodec.read,← read_value]
  cases parsed : (read input).value with
  | none => simp only [decode,parse,parsed,Option.map_none,Option.bind_none]
  | some pair =>
    rcases pair with ⟨opening,rest⟩
    by_cases ended : rest = [] <;> by_cases same : codec.encode (view opening) = input <;>
      simp [decode,parse,parsed,ended,same,encode_value,BytePrefixMatchCost.equal_value]

theorem decode_cost (input : Input) : (decode input).cost ≤ 557*input.length+2400 := by
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
    codec.encode (view opening) = input := by
  have native := decode_value input
  rw [found,Option.map_some] at native
  exact NativeExactCodec.read_sound _ _ _ native.symm

theorem view_injective : Function.Injective view := by
  intro first last same
  have context : first.source.1 = last.source.1 := by
    apply Vector.ext
    intro i hi
    exact congrFun (congrArg NativeGoldBatchMessage.Data.context same) ⟨i,hi⟩
  have root : first.source.2 = last.source.2 := by
    apply Vector.ext
    intro i hi
    exact congrFun (congrArg NativeGoldBatchMessage.Data.root same) ⟨i,hi⟩
  have source := Prod.ext context root
  have queries := congrArg NativeGoldBatchMessage.Data.queries same
  have values := congrArg NativeGoldBatchMessage.Data.values same
  cases first
  cases last
  cases source
  cases queries
  cases values
  rfl

theorem decode_encode (opening : Stored) : (decode (encode opening).value).value = some opening := by
  have accepted : NativeExactCodec.read codec (encode opening).value = some (view opening) := by
    rw [encode_value]
    exact NativeExactCodec.read_encode _ _
  have native := (decode_value (encode opening).value).trans accepted
  cases parsed : (decode (encode opening).value).value with
  | none => rw [parsed,Option.map_none] at native; cases native
  | some values => rw [parsed,Option.map_some] at native; exact congrArg some (view_injective (Option.some.inj native))
end FormalProof4FHE.HasteBoots.StoredBatchMessageCost
