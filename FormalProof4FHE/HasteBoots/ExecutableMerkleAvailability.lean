module
public import FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
public import FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
public import FormalProof4FHE.HasteBoots.FiniteLinearSolver
@[expose] public section

/-! Reconstruct a materialized raw column word from a supplied frozen public
hash log. No oracle queries or classical inverse searches occur at runtime.
Unknown leaf payloads use the existing empty-row fallback. -/
namespace FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeLookupRequestWire (Row)
open NativeGoldColumnAuthentication (encoding)
open BinaryTree MerkleTreeExtractor
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
abbrev Log := QueryLog Input Digest

def view (dummy : Digest) : QueryView Input Unit Digest where
  address _ := ()
  input input := (NativeMerkleRoleDecoders.node.decode input).getD (dummy,dummy)

def resolve (log : Log) (label : Digest) : Option Row :=
  (log.filterMap (fun entry => if entry.2 = label then NativeMerkleRoleDecoders.leaf.decode entry.1 else none)).head?

def reconstruct (height : ℕ) (dummy : Digest) (log : Log) (root : Digest) : Vector Row (2^height) :=
  let partialTree := tree (view dummy) (Skeleton.perfect height) (fun _ => ()) log root
  Vector.ofFn (fun position =>
    (recoverLeaf (resolve log) partialTree (SkeletonLeafIndex.perfectEquiv height position)).getD NativeGoldRawAvailability.emptyRow)

theorem view_eq_analysis (dummy : Digest) : view dummy = (MerkleOracle.model encoding dummy).view := by
  simp only [view,MerkleOracle.model,NativeMerkleRoleDecoders.node_eq_analysis]
  rfl

theorem resolve_eq_analysis (log : Log) : resolve log = MerklePayload.resolve encoding log := by
  funext label
  simp only [resolve,MerklePayload.resolve,MerklePayload.candidates,NativeMerkleRoleDecoders.leaf_eq_analysis]
  rfl

theorem reconstruct_get (height : ℕ) (dummy : Digest) (log : Log) (root : Digest) (position : Fin (2^height)) :
    (reconstruct height dummy log root).get position =
      MerkleAvailability.word encoding dummy NativeGoldRawAvailability.emptyRow height log root position := by
  simp only [reconstruct,FiniteLinearSolver.get_ofFn,view_eq_analysis,resolve_eq_analysis,
    MerkleAvailability.word,MerkleAvailability.payloadAt,MerkleAvailability.tree]
end FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
