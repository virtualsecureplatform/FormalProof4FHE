module

public import VCVio.CryptoFoundations.MerkleTree.ExtractionKernel
public import VCVio.CryptoFoundations.MerkleTree.Hashing.Encoding

@[expose] public section

/-!
# Common-domain unaddressed Merkle hashing

Native nodes hash the ordered concatenation of child digests, without a tree
position. Leaf columns use their own encoding in the SAME hash-input domain.
This interface requires injectivity within each role, not disjoint role images.
Concrete byte encoders and the native path-loop adapter remain separate.
-/

namespace FormalProof4FHE.HasteBoots.MerkleOracle

open OracleSpec

noncomputable section

variable {Input Digest Payload : Type}

abbrev Encoding (Input Digest Payload : Type) :=
  MerkleTreeHashing.QueryEncoding Input Unit Unit Payload Digest

/-- Decode arbitrary queries as node candidates; non-node inputs have a fixed
fallback view. The fallback does not exclude arbitrary adversary queries. -/
def model (enc : Encoding Input Digest Payload) (dummy : Digest) :
    MerkleTreeExtractability.NodeQueryModel Input Unit Digest where
  view.address _ := ()
  view.input input := ((MerkleTreeHashing.RoleDecoder.ofInjective (enc.node ())
    (enc.node_injective ())).decode input).getD (dummy, dummy)
  mkQuery _ children := enc.node () children
  address_mkQuery _ _ := rfl
  input_mkQuery _ children := by
    change ((MerkleTreeHashing.RoleDecoder.ofInjective (enc.node ())
      (enc.node_injective ())).decode (enc.node () children)).getD (dummy, dummy) = children
    rw [(MerkleTreeHashing.RoleDecoder.ofInjective (enc.node ())
      (enc.node_injective ())).decode_encode]
    rfl

/-- Leaf and node requests use identical oracle cells whenever their full
encoded inputs coincide. No extra role tag is introduced by this model. -/
theorem same_cell (enc : Encoding Input Digest Payload) (payload : Payload)
    (children : Digest × Digest) (equal : enc.leaf () payload = enc.node () children) :
    (Input →ₒ Digest).query (enc.leaf () payload) =
      (Input →ₒ Digest).query (enc.node () children) := by
  rw [equal]

end

end FormalProof4FHE.HasteBoots.MerkleOracle
