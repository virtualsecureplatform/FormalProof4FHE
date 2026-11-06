module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsWire
public import FormalProof4FHE.HasteBoots.NativeByteCodec
public import FormalProof4FHE.HasteBoots.NativeExactCodec
@[expose] public section

/-! Exact structural codec for the native bind_many message. Raw query/value
words are retained. Recognizing this message is not a trusted-parameter check
or a strict native proof deserializer/refinement theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchMessage
open NativePrefixCodec (Codec Vector product vector transport)
open NativeRootMessage (Digest)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)

structure Data where
  context : Digest
  root : Digest
  queries : Vector Query
  values : Vector Row

def equiv : (Digest × Digest × Vector Query × Vector Row) ≃ Data where
  toFun := fun data => ⟨data.1,data.2.1,data.2.2.1,data.2.2.2⟩
  invFun := fun data => (data.context,data.root,data.queries,data.values)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def codec : Codec Data := transport (product NativeByteCodec.digest (product NativeByteCodec.digest
  (product (vector NativeGoldPcsWire.queryCodec) (vector NativeLookupRequestWire.rowCodec)))) equiv

theorem encode (data : Data) : codec.encode data = List.ofFn data.context ++ List.ofFn data.root ++
    (vector NativeGoldPcsWire.queryCodec).encode data.queries ++ (vector NativeLookupRequestWire.rowCodec).encode data.values := by
  simp only [codec,transport,product,equiv,NativeByteCodec.digest_encode]
  rfl

theorem read_prefix (data : Data) (suffix : InputIndexedOracle.Input) :
    codec.read (codec.encode data ++ suffix) = some (data,suffix) := codec.read_encode data suffix

theorem read_exact (data : Data) : NativeExactCodec.read codec (codec.encode data) = some data := NativeExactCodec.read_encode codec data

theorem trailing_rejected (data : Data) (suffix : InputIndexedOracle.Input) (nonempty : suffix ≠ []) :
    NativeExactCodec.read codec (codec.encode data ++ suffix) = none := by
  simp only [NativeExactCodec.read,read_prefix,Option.bind_some,nonempty,false_and,ite_false]
end FormalProof4FHE.HasteBoots.NativeGoldBatchMessage
