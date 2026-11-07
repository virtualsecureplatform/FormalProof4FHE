module
public import FormalProof4FHE.HasteBoots.GoldQueryWireCost
@[expose] public section

/-! Closed measured codecs for the outer query vector in an original Gold batch
message. Every nested matrix is read and retained, including empty vectors and
raw words. These bounds describe the explicit operation model, not native runtime. -/
namespace FormalProof4FHE.HasteBoots.GoldBatchQueriesCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)

abbrev Queries := NativePrefixCodec.Vector NativeGoldPcsWire.Query

def weight (queries : Queries) :=
  VectorWireReadCost.weight GoldQueryWireCost.queryWeight queries.val

def read (input : Input) : Run (Option (Queries × Input)) :=
  VectorWireReadCost.read GoldQueryWireCost.read input

private theorem element_cost (input : Input) :
    (GoldQueryWireCost.read input).cost ≤ 139*(input.length+1) := by
  have bound := GoldQueryWireCost.read_cost input
  omega

private theorem element_success (input : Input) (query : NativeGoldPcsWire.Query) (rest : Input)
    (found : (GoldQueryWireCost.read input).value = some (query,rest)) :
    (GoldQueryWireCost.read input).cost ≤ 139*(input.length-rest.length)+1 := by
  have bound := GoldQueryWireCost.read_success_cost input query rest found
  omega

private theorem element_progress (input : Input) (query : NativeGoldPcsWire.Query) (rest : Input)
    (found : (GoldQueryWireCost.read input).value = some (query,rest)) : rest.length < input.length := by
  have bound := GoldQueryWireCost.read_size input query rest found
  omega

theorem read_value (input : Input) :
    (read input).value = (NativePrefixCodec.vector NativeGoldPcsWire.queryCodec).read input :=
  VectorWireReadCost.read_value GoldQueryWireCost.read NativeGoldPcsWire.queryCodec
    GoldQueryWireCost.read_value input

theorem read_size (input : Input) (queries : Queries) (rest : Input)
    (found : (read input).value = some (queries,rest)) : weight queries+rest.length+1 ≤ input.length :=
  VectorWireReadCost.read_size GoldQueryWireCost.read GoldQueryWireCost.queryWeight
    GoldQueryWireCost.read_size input queries rest found

theorem read_cost (input : Input) : (read input).cost ≤ 145*(input.length+1)+3 :=
  VectorWireReadCost.read_cost GoldQueryWireCost.read 139 (by decide)
    element_cost element_success element_progress input

theorem read_success_cost (input : Input) (queries : Queries) (rest : Input)
    (found : (read input).value = some (queries,rest)) :
    (read input).cost ≤ 145*(input.length-rest.length)+1 :=
  VectorWireReadCost.read_success_cost GoldQueryWireCost.read 139 (by decide)
    element_success element_progress input queries rest found

def encode (queries : Queries) : Run Input :=
  VectorWireEncodeCost.encode GoldQueryWireCost.encode queries

private theorem element_encode_cost (query : NativeGoldPcsWire.Query) :
    (GoldQueryWireCost.encode query).cost ≤ 343*(GoldQueryWireCost.queryWeight query+1) := by
  have bound := GoldQueryWireCost.encode_cost query
  omega

theorem encode_value (queries : Queries) :
    (encode queries).value = (NativePrefixCodec.vector NativeGoldPcsWire.queryCodec).encode queries :=
  VectorWireEncodeCost.encode_value GoldQueryWireCost.encode NativeGoldPcsWire.queryCodec
    GoldQueryWireCost.encode_value queries

theorem encode_cost (queries : Queries) : (encode queries).cost ≤ 379*weight queries+93 :=
  VectorWireEncodeCost.encode_cost GoldQueryWireCost.encode GoldQueryWireCost.queryWeight 343
    element_encode_cost GoldQueryWireCost.encode_size queries

theorem encode_size (queries : Queries) : (encode queries).value.length ≤ 9*(weight queries+1) :=
  VectorWireEncodeCost.encode_size GoldQueryWireCost.encode GoldQueryWireCost.queryWeight
    GoldQueryWireCost.encode_size queries
end FormalProof4FHE.HasteBoots.GoldBatchQueriesCost
