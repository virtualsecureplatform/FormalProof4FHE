module
public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
public import FormalProof4FHE.HasteBoots.CostedMerkleLeaf
public import FormalProof4FHE.HasteBoots.CostedMerkleNode
@[expose] public section

/-! Executable, fail-closed partial inverses for actual Merkle hash inputs.
Canonical re-encoding is checked explicitly; prefix readability alone does not
establish membership in a hash role. Leaf and node roles still share one oracle. -/
namespace FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeLookupRequestWire (Row rowCodec)
open NativeGoldColumnAuthentication (leafInput nodeInput)
open MerkleTreeHashing (RoleDecoder)

/-- Guard any complete parser with equality to the exact role encoding. -/
def guarded {A : Type} (encode : A → Input) (parse : Input → Option A)
    (roundtrip : ∀ value, parse (encode value) = some value) : RoleDecoder encode where
  decode input := (parse input).bind (fun value => if encode value = input then some value else none)
  decode_encode value := by simp [roundtrip]
  encode_decode input value found := by
    simp only [Option.bind_eq_some_iff] at found
    obtain ⟨parsed,_,found⟩ := found
    split_ifs at found with equal
    · cases found
      exact equal

/-- Sound partial inverses of the same encoding agree on arbitrary inputs. -/
theorem decode_unique {A : Type} {encode : A → Input} (left right : RoleDecoder encode) :
    left.decode = right.decode := by
  funext input
  cases first : left.decode input with
  | none =>
    cases second : right.decode input with
    | none => rfl
    | some value =>
      have accepted := left.decode_encode value
      rw [right.encode_decode input value second,first] at accepted
      contradiction
  | some value =>
    rw [← left.encode_decode input value first,right.decode_encode]

def parseLeaf (input : Input) : Option Row :=
  if input.take NativeFieldWire.columnDomain.length = NativeFieldWire.columnDomain then
    (rowCodec.read (input.drop NativeFieldWire.columnDomain.length)).bind (fun parsed =>
      if parsed.2 = [] then some parsed.1 else none)
  else none

theorem parseLeaf_encode (row : Row) : parseLeaf (leafInput row) = some row := by
  have parsed := rowCodec.read_encode row []
  simp only [List.append_nil] at parsed
  simp only [parseLeaf,leafInput,List.take_left,List.drop_left,ite_true,parsed,Option.bind_some]

def leaf : RoleDecoder (leafInput) where
  decode input := (CostedMerkleLeaf.decode input).value
  decode_encode row := by
    rw [CostedMerkleLeaf.decode_value]
    exact (guarded leafInput parseLeaf parseLeaf_encode).decode_encode row
  encode_decode input row found := by
    rw [CostedMerkleLeaf.decode_value] at found
    exact (guarded leafInput parseLeaf parseLeaf_encode).encode_decode input row found

theorem leaf_decode_eq_reference (input : Input) :
    leaf.decode input = (guarded leafInput parseLeaf parseLeaf_encode).decode input :=
  CostedMerkleLeaf.decode_value input

def parseNode (input : Input) : Option (Digest × Digest) :=
  ((NativePrefixCodec.product NativeByteCodec.digest NativeByteCodec.digest).read input).bind
    (fun parsed => if parsed.2 = [] then some parsed.1 else none)

theorem parseNode_encode (pair : Digest × Digest) : parseNode (nodeInput pair.1 pair.2) = some pair := by
  have parsed := (NativePrefixCodec.product NativeByteCodec.digest NativeByteCodec.digest).read_encode pair []
  simp only [List.append_nil] at parsed
  change (NativePrefixCodec.product NativeByteCodec.digest NativeByteCodec.digest).read (nodeInput pair.1 pair.2) = some (pair,[]) at parsed
  unfold parseNode
  rw [parsed]
  rfl

def node : RoleDecoder (fun pair : Digest × Digest => nodeInput pair.1 pair.2) where
  decode input := (CostedMerkleNode.decode input).value
  decode_encode pair := by
    rw [CostedMerkleNode.decode_value]
    exact (guarded _ parseNode parseNode_encode).decode_encode pair
  encode_decode input pair found := by
    rw [CostedMerkleNode.decode_value] at found
    exact (guarded _ parseNode parseNode_encode).encode_decode input pair found

theorem node_decode_eq_reference (input : Input) :
    node.decode input = (guarded _ parseNode parseNode_encode).decode input :=
  CostedMerkleNode.decode_value input

theorem leaf_eq_analysis : leaf.decode =
    (RoleDecoder.ofInjective leafInput (NativeGoldColumnAuthentication.encoding.leaf_injective ())).decode :=
  decode_unique _ _

theorem node_eq_analysis : node.decode =
    (RoleDecoder.ofInjective (fun pair : Digest × Digest => nodeInput pair.1 pair.2)
      (NativeGoldColumnAuthentication.encoding.node_injective ())).decode :=
  decode_unique _ _
end FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
